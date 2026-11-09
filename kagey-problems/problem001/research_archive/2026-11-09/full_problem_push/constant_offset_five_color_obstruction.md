# A parallel-offset block can require five P colors

9 November 2026. The fixed-offset route has a genuine \(K_5\) obstruction.
Thus a universal refinement using at most four colors cannot work.
This does not prove that the required palette is unbounded.

For fixed \(u=a-b\), two odd-row positions differing by an even integer
\(d\) conflict when one of
\[
(u+d)^2+4d^2,\qquad(u-d)^2+4d^2
\]
is a square, with its vertical completion inside the strip.

For \(u=1045\), take relative odd-row positions
\[
0,\quad70,\quad450,\quad520,\quad868.
\]
Every pair conflicts. The following table lists the directed source and
target positions and the hypotenuse. Direction matters because the source
uses its odd endpoint and the target its even endpoint.

| Source | Target | Hypotenuse |
|---:|---:|---:|
| 0 | 70 | 985 |
| 450 | 0 | 1745 |
| 0 | 520 | 1165 |
| 0 | 868 | 1745 |
| 450 | 70 | 1615 |
| 520 | 70 | 1745 |
| 70 | 868 | 1615 |
| 450 | 520 | 985 |
| 450 | 868 | 1045 |
| 520 | 868 | 985 |

For each row of the table,
\[
4(\mathrm{source}-\mathrm{target})^2+
(1045+\mathrm{source}-\mathrm{target})^2=L^2.
\]
Adding the odd-row shift 1171 gives the five actual parity labels
\[
(1171,126),\ (1241,196),\ (1621,576),\
(1691,646),\ (2039,994).
\]
Place them at columns \(0,140,900,1040,1736\). Every vertical completion
in the table fits in height 2039. The smallest completion row is one,
and the largest is 1955. Therefore this is an actual in-strip \(K_5\),
not only a relaxed arithmetic conflict graph.

A smaller \(K_4\) occurs for offset 55 at relative positions \(0,8,30,50\).
The labels
\[
(77,22),(85,30),(107,52),(127,72)
\]
at columns \(0,16,60,100\) realize it inside height 147.

The standard-library checker verify_constant_offset_cliques.py verifies
all square identities, parity conditions, and completion bounds. Its
full coordinates are saved in constant_offset_clique_certificates.json.
The certificates prove lower bounds of five and four colors respectively.
They leave a uniform palette of five or more colors open.

