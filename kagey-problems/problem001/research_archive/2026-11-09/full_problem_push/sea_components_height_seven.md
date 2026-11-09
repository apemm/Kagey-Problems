# Exact recurrent components at height seven

9 November 2026. All balanced seven-row partitions have now been compared.
Ordinary parity is not the maximizing partition. The unique maximizing
reflection class is \(\{1,3,6\}\mid\{2,4,5,7\}\). Its complete graph has one
recurrent boundary component, making the full seven-row counting asymptotic
unconditional.

| Row partition | Reachable residual states | Recurrent states | Transient singleton components | Certified Perron interval |
|---|---:|---:|---:|---|
| Parity | 17,463,676 | 16,886,304 | 577,372 | \(3.776799\le\rho_7\le3.776801\) |
| \(\{1,4,5\}\mid\{2,3,6,7\}\) | 9,497,416 | 9,220,131 | 277,285 | \(3.499308\le\rho_Q\le3.499309\) |
| \(\{1,3,6\}\mid\{2,4,5,7\}\) | 12,928,518 | 12,630,235 | 298,283 | \(3.780928\le R_7\le3.780929\) |
| \(\{1,4,6\}\mid\{2,3,5,7\}\) | 14,422,194 | 14,058,285 | 363,909 | \(3.776961\le\rho_{146}\le3.776962\) |

The displayed bounds are exact rational inequalities with denominator one
million. Floating-point iteration was used only to propose positive integer
vectors for those inequalities.

## Exact graph and independent checks

The forbidden-support compiler enumerates actual tilted rectangles, all virtual
axis rivals for the chosen complete balanced pair set, and tilted-pair
collisions. Its residual automaton stores inclusion-minimal unmatched future
requirements. It does not enumerate full history words.

The native transition and SCC implementation is independently reviewed in
[native_sea_and_fiber_independent_audit.md](native_sea_and_fiber_independent_audit.md).
The packed representation interns 256-bit residual blocks and compares full
keys after every hash match. Hash collisions cannot merge states. Packed
checkpoints also authenticate the complete exported transition table by SHA256.

At heights four, five, and six, the packed builder reproduces every labeled
transition of the earlier exact implementation, including state identifiers.
The height-six checkpoint/resume test reproduces the same complete graph.

The height-seven parity graph contains 67,269,202 accepted labeled edges. An
independent checker verifies every edge against the claimed component order.
It proves that the large component is strongly connected by reachability in
both directions from a constant-row state. Every other component is a
singleton, has no self-loop, and lies in the strictly ordered component DAG.
Thus these other states are transient. The check is recorded in
[sea_packed_h7.scc_verified.json](sea_packed_h7.scc_verified.json).

The independent integer spectral checker verifies all 16,886,304 recurrent
parity states and all 9,220,131 recurrent quadratic states. It checks
\[
 L v_i\le (Tv)_i\le U v_i
\]
for a strictly positive integer vector on the component. The certificate
denominators and an explicit overflow bound make every verification an exact
integer calculation:

* [Parity spectral certificate](sea_packed_h7.perron.307694.verified.json)
* [Quadratic spectral certificate](sea_packed_h7_p145.perron.194287.verified.json)
* [Independent SCC checker](verify_sea_scc.py)
* [Independent spectral checker](verify_sea_perron.py)

The binary parity graph has SHA256

3264BC24053B20ADF7B44EE2631905AA75987306E99DD2F781FC9394A0141E2B.

The quadratic graph has SHA256

4F078650B1486783C0876FB9C6BDA2E8194331AC93B73C253E023740BD7B6116.

## Counting consequence and boundary convention

All constant parity states are in the unique recurrent component, whose
self-loops make it primitive. Every parity double has a positive insertion
bridge through that component. Hence the contribution of completed
seven-row parity equality boards has the unconditional asymptotic
\[
 b_{\rm parity}(m)\sim
 B_7\left(\prod_{e\in E_{\rm parity}}\kappa_e\right)
 m^{12}\rho_7^m,
 \qquad B_7>0,\quad \kappa_e>0.
\]
Here the boundary and insertion constants use the exact end-aware model from
the earlier counting theorem. The normalized residual graph is used for its
recurrent components and spectral radius.

Normalized positive supports can reject a finite prefix because a shared
rectangle corner would lie beyond that prefix. This changes finite endpoint
acceptance, but not the bi-infinite sea language or its recurrent components.
Therefore the residual graph must not be used with arbitrary terminal states
to calculate the boundary constant.

The displayed parity contribution is not the full asymptotic: two nonparity
reflection classes have strictly larger entropy.

## Complete partition comparison

Every balanced partition has a unique class of three rows. There are
\(\binom73=35\) such classes, or 19 after row reflection. For each class
other than 136, 146, and parity 246, it suffices to omit forbidden supports
of span greater than ten. This enlarges the sea shift, so the resulting
spectral radius is a rigorous upper bound for that partition.

Every selected graph was completed, its recurrent-component certificate
independently checked, and its integer Collatz inequalities independently
verified. The complete [comparison certificate](height_seven_partition_comparison.json)
also regenerates the 35 classes and their reflection orbits.

| Three-row class | Certified entropy upper bound | Model |
|---|---:|---|
| 123 | 3.604771 | Span-ten upper model |
| 124 | 3.631203 | Span-ten upper model |
| 125 | 3.501029 | Span-ten upper model |
| 126 | 3.637069 | Span-ten upper model |
| 127 | 3.353170 | Span-ten upper model |
| 134 | 3.734202 | Span-ten upper model |
| 135 | 3.767617 | Span-ten upper model |
| 136 | 3.780929 | Complete graph; lower bound 3.780928 |
| 137 | 3.575569 | Span-ten upper model |
| 145 | 3.515941 | Span-ten upper model |
| 146 | 3.776962 | Complete graph |
| 147 | 3.367013 | Span-ten upper model |
| 156 | 3.595081 | Span-ten upper model |
| 234 | 3.590164 | Span-ten upper model |
| 235 | 3.469288 | Span-ten upper model |
| 236 | 3.559212 | Span-ten upper model |
| 245 | 3.681326 | Span-ten upper model |
| 246 | 3.776801 | Complete parity graph |
| 345 | 3.468921 | Span-ten upper model |

The lower bound for 136 exceeds every other upper bound. Thus the only
maximizing labeled partitions are 136 and its reflection 257.

## The full counting asymptotic

Write \(\pi=\{1,3,6\}\mid\{2,4,5,7\}\), and let \(R_7\) be its Perron
root. Its unique recurrent component contains constant states, so it is
primitive. Every one of its twelve double labels has a positive insertion
bridge. The end-aware marked-transfer theorem therefore gives
\[
 a_7(m)\sim C_7m^{12}R_7^m,\qquad C_7>0.          \tag{1}
\]
The two maximizing partitions are exchanged by row reflection, so their
leading constants are equal. If
\[
 b_\pi(m)\sim B_\pi
       \left(\prod_{e\in E_\pi}\kappa_e\right)m^{12}R_7^m
\]
uses the full end-aware boundary normalization, then
\[
 C_7=2B_\pi\prod_{e\in E_\pi}\kappa_e.            \tag{2}
\]
All factors are positive. Fixed-collar constants have their separate
length normalization and must not be substituted for \(B_\pi\).

The relative error in (1) is \(O(1/m)\). More precisely, the rational
end-aware generating function gives a polynomial \(P_7\) of degree twelve
and a number \(\theta<R_7\) such that
\[
 a_7(m)=R_7^mP_7(m)+O(\theta^m),\qquad
 [m^{12}]P_7=C_7.
\]
The primitive maximizing component supplies the only peripheral
eigenvalue at radius \(R_7\), and all other partitions have strictly
smaller radii. Possible polynomial factors at those smaller radii are
absorbed by choosing \(\theta\) slightly larger than them.

This proves the seven-row formula without an ordinary-parity dominance
hypothesis. Arbitrary-height boundary-component dominance and selection
of the maximizing partition remain open.
