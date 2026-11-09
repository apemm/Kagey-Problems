# Local arithmetic densities for the ordinary and quadratic phases

9 November 2026. These exact residue calculations compare three protected column laws:
\[
 {\rm O}:y\equiv0\pmod2,\qquad
 {\rm C}:x+y\equiv0\pmod2,\qquad
 {\rm Q}:q(x)+q(y)\equiv0\pmod2,
 \quad q(n)=n(n-1)/2.
\]
They do not by themselves compare the sea entropies. Turning them into entropy coefficients requires asymptotic geometric counts, deletion of duplicate or implied supports, and a controlled expansion for avoidance probabilities.

## 1. A translation formula

Let \(S=\{v_0,\ldots,v_{s-1}\}\subset\mathbb Z^2\), translate so \(v_0=0\), and average its placement \(P\) uniformly modulo four in each coordinate. Put \(Q(x,y)=q(x)+q(y)\). Since
\[
 Q(P+v)=Q(P)+Q(v)+P\cdot v,
\]
the fraction of translations for which every point of \(P+S\) satisfies phase Q is
\[
 \frac18
 \#\left\{\ell\in\mathbb F_2^2:
       Q(v_i)+\ell\cdot v_i=0\text{ for every }i\right\}.
\tag{1}
\]
For each fixed \(P\bmod2\), exactly half its four lifts modulo four have \(Q(P)=0\). Formula (1) follows.

For O or C, the analogous fraction is \(1/2\) if the relevant linear functional vanishes on every \(v_i\), and zero otherwise.

## 2. Hidden rectangles

Write the adjacent vectors as
\[
 k(a,b),\qquad l(-b,a),\qquad (a,b)=1,
\]
and average \(k,l\) independently modulo four and the base point modulo four. A residue zero for a scale represents a positive multiple of four, not a degenerate side.

The exact acceptance fractions are
\[
\begin{array}{c|ccc}
 (a,b)\bmod2&{\rm O}&{\rm C}&{\rm Q}\\ \hline
 (1,1)&1/8&1/2&1/4\\
 (1,0)\text{ or }(0,1)&1/4&1/8&1/8.
\end{array}
\tag{2}
\]

For O, both vertical side components must be even. For C, both differences between vertical and horizontal side components must be even. These give the first two columns immediately.

For Q, if \(a,b\) are odd, two odd scales give incompatible equations on the base parity. Two even scales impose no additional condition beyond the base phase. Exactly one odd scale imposes one additional base-parity equation. The resulting average is \(1/4\).

If \(a,b\) have opposite parity, an even scale must be divisible by four for its side to preserve Q. An odd scale imposes one base-parity equation; its right side changes when the scale changes by two. Averaging these four cases gives \(1/8\).

As a formal average with primitive-direction proportions \(1/3\) and \(2/3\), (2) gives
\[
 {\rm O}:5/24,\qquad {\rm C}:1/4,\qquad {\rm Q}:1/6.
\tag{3}
\]
Those are arithmetic densities. A geometric weighted sum still requires justification that these proportions and scale residues are equidistributed for the particular count under study.

## 3. Two rectangles sharing a missing corner

For a rectangle through a fixed corner already in the phase, the scale-averaged compatibility probabilities are
\[
\begin{array}{c|ccc}
 (a,b)\bmod2&{\rm O}&{\rm C}&{\rm Q}\\ \hline
 (1,1)&1/4&1&1/2\\
 (1,0)\text{ or }(0,1)&1/2&1/4&1/4.
\end{array}
\tag{4}
\]
For Q, these conditional averages are independent of the fixed corner's parity. Hence for two independently averaged scale pairs, multiply the corresponding entries of (4), then multiply by \(1/2\) for the common corner's phase.

This also counts phase-compatible six-cell supports: the three selected corners of either rectangle force its missing corner into the same phase, so compatibility of the six nonshared corners is equivalent to compatibility of both whole rectangles.

The exact table is
\[
\begin{array}{c|ccc}
 \text{two primitive-direction types}&{\rm O}&{\rm C}&{\rm Q}\\ \hline
 (1,1),(1,1)&1/32&1/2&1/8\\
 (1,1),\text{opposite parity}&1/16&1/8&1/16\\
 \text{opposite parity},\text{opposite parity}&1/8&1/32&1/32.
\end{array}
\tag{5}
\]
With independently weighted direction types in proportions \(1/3,2/3\), the formal averages are
\[
 {\rm O}:25/288,\qquad {\rm C}:1/8,\qquad {\rm Q}:1/18.
\tag{6}
\]
The quadratic-to-ordinary ratio is \(16/25\).

A six-cell geometric count must still discard pairs that share another corner or request two different rows in one column. Equation (5) is the residue factor before those geometric exclusions.

## 4. A generic mixed side/diagonal orbit

Normalize the common white side to \(0,U\). Put
\[
 U=k(a,b),\quad T=l(-b,a),\quad |V|=|U|,\quad V\equiv U\pmod2.
\]
The four required black points are
\[
 T,\quad T+U,\quad (U+V)/2,\quad (U-V)/2.
\tag{7}
\]

Take a generic eight-element sign-and-coordinate-swap orbit of \(V\), excluding the orbit containing the degenerate choices \(V=\pm U\). Average over its members that satisfy the integrality condition \(V\equiv U\pmod2\), over \(l\bmod4\), and over the base translation modulo four.

Let \(\nu=\nu_2(k)\). The exact fractions are
\[
\begin{array}{c|c|ccc}
(a,b)\bmod2&\nu&{\rm O}&{\rm C}&{\rm Q}\\ \hline
(1,1)&0&0&1/4&1/8\\
(1,1)&1&1/4&1/2&1/4\\
(1,1)&\ge2&1/4&1/2&3/8\\ \hline
(1,0)&0&1/4&0&1/8\\
(1,0)&1&1/4&1/4&0\\
(1,0)&\ge2&1/4&1/4&1/4\\ \hline
(0,1)&0&0&0&1/8\\
(0,1)&1&1/4&1/4&0\\
(0,1)&\ge2&1/2&1/4&1/4.
\end{array}
\tag{8}
\]

One useful identity behind the Q column is
\[
 Q(T)+Q(T+U)+Q((U+V)/2)+Q((U-V)/2)=0\pmod2.
\tag{9}
\]
Indeed \(T\cdot U=0\), and the two half-diagonal points are perpendicular because \(|U|=|V|\). Formula (1), together with sign changes of \(V\), then gives (8).

For opposite-parity primitive directions with odd \(k\), only half of a generic eight-element orbit satisfies \(V\equiv U\pmod2\). For even \(k\), every orbit member does. This factor must be included before averaging over \(\nu\). It would be incorrect to average the rows of (8) with unweighted scale frequencies and treat the result as the mixed-support coefficient.

The divisor weights coming from the number of circle representations also need to be retained. No leading mixed coefficient is asserted here.

## 5. Verification and remaining work

The integer residue checker in [check_phase_local_densities.py](check_phase_local_densities.py) verifies (2), (5), and representative generic orbits in (8). The calculations use actual perpendicular vectors and exact equal-norm representations; they do not enumerate sea states or components.

The tables show that the quadratic phase is not uniformly worse than ordinary parity even at the level of the elementary obstruction families. In particular, (2) and (5) have smaller formally averaged Q densities. This is a reason to test partition dominance, not a proof that the quadratic partition wins.

The remaining analytic steps are substantial:

1. Obtain the weighted asymptotics for minimal four- and six-cell supports, including their 2-adic local factors.
2. Bound overlaps sharply enough to turn support weights into an entropy expansion.
3. Control mixed-parity excursions in the ordinary canonical component; comparing only its affine sublanguages would not compare \(\lambda_*\) itself.

Until those steps are proved, the exact ordering of the ordinary and quadratic boundary components remains open.

