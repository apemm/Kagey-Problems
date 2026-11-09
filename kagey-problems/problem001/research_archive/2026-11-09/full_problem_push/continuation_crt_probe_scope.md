# Scope of the continuation CRT probes

9 November 2026. The scripts in this note are exploratory arithmetic
searches. They do not validate the full CRT scaffold or a filled board.

## Vertical geometries up to a prescribed height

[probe_crt_vertical_rivals.py](probe_crt_vertical_rivals.py) enumerates
primitive Pythagorean triangles and their allowed odd dilations. For
slope \(P/Q\), it retains \(D=Pk\), \(\Delta a=Qk\), an odd offset t,
and the exact vertical-completion containment conditions. Horizontal
displacements must be multiples of 98. Its label-incidence statistic
unions the allowed translation intervals, so multiple rivals at the
same label are not counted as separate labels.

The saved outputs are
[the initial ranges](continuation_crt_vertical_probe.json),
[the larger rational-slope ranges](continuation_crt_rational_large_probe.json),
and [the larger slope-one ranges](continuation_crt_slope_one_large_probe.json).

At height 1048576, the \(4/3\) run found 38452 normalized geometries,
27543 unsafe odd offsets, and 8713692364 incident labels out of
274877906944 possible parity labels. This finite ratio is about 0.0317.
It is not an asymptotic density estimate. In particular, the proved
[positive-density unsafe-chain family](crt_scaffold_independent_reductions.md)
rules out treating unsafe chains as a zero-density exception.

## Exact distance graphs for split slope four thirds

For a fixed positive odd t, an integer k is a forbidden directed
distance exactly when
\[
 25k^2+6tk+t^2=L^2.
\]
Factoring gives
\[
 A=5L-25k-3t,\qquad B=5L+25k+3t,\qquad AB=16t^2.
\]
For even k, L is odd. Since \(A+B=10L>0\), both factors are positive,
and their 2-adic valuations are one and three in some order.
Thus every distance is obtained by taking
\[
 A=2d\ \hbox{or}\ 8d,\quad d\mid t^2,\qquad
 B=16t^2/A,\qquad k=(B-A-6t)/50,
\]
and checking integrality. This is a finite, exhaustive arithmetic
parametrization for fixed t.

[probe_rational_crt_chain_cliques.py](probe_rational_crt_chain_cliques.py)
forms the undirected distance set from both signs of k. A clique can
be translated to have its least vertex zero; its remaining vertices
belong to the positive distance set. The script therefore finds the
largest clique in that finite difference graph by exact backtracking.

There are two search normalizations:

- Step 98 imposes \(98\mid k\) directly.
- Step 2 imposes only even k, then multiplies t and k by 49 when
  constructing the actual CRT certificate.

Both completed searches through every positive odd \(t\le500001\)
found maximum clique size four. They did not compute chromatic numbers.
They say nothing about larger t or the chromatic number of the
[countable rational graph](crt_chain_cayley_equivalence.md).

The outputs are
[step 98](continuation_rational_chain_cliques_large.json) and
[step 2](continuation_rational_chain_cliques_normalized.json).
The step-2 record occurs first at normalized t=375, becoming physical
offset 18375 after scaling. The actual in-strip \(K_4\), at height 62182,
has a separate [exact checker](verify_crt_cayley_k4.py) and
[independent audit](crt_chain_cayley_independent_audit.md).

Subsequent coloring certificates go beyond the clique searches.
At normalized t=375 the graph on vertices zero through 149 has 1,289
edges and cannot be colored with five colors. Every proof addition
passes independent reverse unit propagation. The complete graph is
realized inside the strip at height 80,998.
Thus the actual P-chain requires at least six colors, although its
largest clique in the preceding search has size four.
The [certificate audit](crt_chain_chromatic_independent_audit.md)
records the exact embedding and proof checks. Bounded colorability
of the infinite graph remains open.

All probe jobs described here completed. The independently checked
certificates, rather than absence of examples in a bounded search,
support the proved obstruction statements.

