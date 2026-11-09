# Independent audit of polylogarithmic packet separation

9 November 2026. The estimates and deductions in
[polylogarithmic_packet_separation.md](polylogarithmic_packet_separation.md)
pass independent review, with distances understood to lie within the
geometric memory \(L=Ch^2\). This is a theorem for the specified
packet class, not a classification of arbitrary phase profiles.

For the diagonal kernel, put \(t=z-d\). If \(z>d\), the norm equation
gives \(t\le\sqrt{d^2+h^2}-d\le\min(h,h^2/d)\).
If \(z<d\), it gives \(-t\le\min(d,h^2/d)\le h\).
Thus the same stated bound holds for both signs. The factor
\(2d+t=d+z\) is positive, and the nonzero product
\((v-w)(v+w)=t(2d+t)\) has at most a constant times
\(\tau(|t|)\tau(2d+t)\) signed factor pairs.

In a distance interval of length \(\ell\le D\), the integers
\(2d+t\) are \(O(\max(h,D))\). Divisor pairing restricts the small
factor to the square root of that bound. A congruence in \(d\)
has at most two residue classes, since its coefficient is two.
Summing their counts proves the interval estimate, including
the square-root error. After summing \(\tau(|t|)\) and dividing
by \(h^2\), both terms in the stated diagonal kernel follow.

For a selected distance set of cardinality \(O(D/g)\), the map
\(d\mapsto2d+t\) is injective. Cauchy--Schwarz against the full
second divisor moment therefore gives
\(O(\sqrt{D\max(h,D)/g}\,\Lambda^{3/2})\).
Summing over \(t\) gives the factor \(\sqrt{D/h}\) below \(h\)
and a constant above it. The lower dyadic scales sum geometrically,
and the upper scales contribute only \(O(\Lambda)\) intervals.
This verifies the total \(\Lambda^{7/2}/\sqrt g\) bound.
The side kernel follows from the same argument applied to
\(\tau(d)/d\). Enlarging the cardinality by \(A\Lambda\) introduces
only \(\sqrt{A\Lambda}\).

Disjoint packet expansions justify both sparse cardinality bounds.
A free black point lies in at most one expanded interval. For every
other interval at distance \(D\), its expansion length is \(O(D)\),
and disjoint half-expansions fit in an interval of length \(O(D)\).
For the possible nearby packet, the smaller excluded buffer ensures
\(D\ge A\ell\Lambda\), so the interval kernel is applicable.
Its diagonal contribution is \(o(1)\) uniformly for
\(\ell\le h/\Lambda^3\). The other-packet buffer loss is
\(O(\sqrt A/\Lambda)=o(1)\).

The direction cutoff satisfies
\(\log R\ge\frac12\log(h/\ell)\) for all allowed widths once
\(h\) is sufficiently large. The remaining conditional comparison
uses the previously audited root and bulk estimates; replacing
their former maximum-divisor input by the new kernel preserves
all required small one-cell extension bounds. The fixed small
marking rate controls the global two-cell extension bound.
The new root penalty dominates the restored old bulk and
alphabet-size terms.

Finally, under the explicit internal-density condition,
\(\log(e\ell/q)\le1+B_0\log\Lambda\), whereas the penalty per
error is at least a constant times \(\log^2\Lambda\).
The activity is therefore at most a geometric tail starting at
\(q_{\min}\). The function
\(\ell\log^2(h/\ell)\) is increasing in the entire relevant range
above \(\Lambda^{B_0}\); below it, \(\log(h/\ell)\sim\log h\).
This verifies the uniform \(\exp(-c_{B_0}\log^2h)\) activity bound.

The internal-density condition is used only when summing packet
descriptions. The fixed-description relative estimate does not
need that condition. Neither conclusion includes densely interacting
packets or unrestricted macroscopic phase patterns.

## Packets inside protected domains

The later
[polylog_packets_in_protected_domains.md](polylog_packets_in_protected_domains.md)
also passes this review. The new distance-dependent direction cutoff
keeps each active root entirely within its protected domain. Its
logarithm is bounded below by a fixed fraction of the minimum of
\(\log(h/\ell)\) and \(\log(D/h)\), because both are at least a
fixed positive multiple of \(\log\log h\).

The maximum expanded packet radius is \(h\Lambda^7\), which is
smaller than the guard distance \(H=h\Lambda^8\). Disjoint
expansions therefore give total guard width \(O(h/\Lambda^2)\)
per assigned wall. Counting actual guard-error subsets costs
\(\exp(o(h))\), even when the wall neighborhoods overlap.

The active activity splits into the width penalty and the
distance penalty using \(e^{-\min(A,B)}\le e^{-A}+e^{-B}\).
Internal density pays the binomial entropy in both terms.
The distance-dependent contribution per start is bounded by
\(C\Lambda^{B_0}\exp[-c\log^2(d/(C'h))]\).
After the substitution \(v=\log(d/(C'h))\), its sum beyond the
guard distance is \(o(h)\) per wall. This accounts for all
near-wall descriptions without requiring a global error-density
bound.

The earlier jointly marked row, wall, and packet comparison then
applies with these smaller cutoffs. Guard losses and the
distance-dependent activities are absorbed by the actual wall
penalty; active penalties absorb the bounded row-root loss at
errors. This proves the stated row comparison in the restricted
language.

For the leading-pressure assertion, avoiding the truncated bulk
before the packet roots retains coefficient one on the bulk mean.
The guard bulk deletion is \(O(J\Lambda^2)\). At wall density
\(O(\Lambda^4/h^2)\), that loss, the \(o(h)\) wall decorations,
and the finite-span cut loss are all \(o(m\Lambda^4/h)\).
Larger wall densities are excluded by the absolute wall estimate.
The stated order of limits preserves the small truncation loss.
The resulting comparison with the quadratic protected phase is
therefore valid for this enlarged domain-and-packet class.

Minimum domain lengths, disjoint expanded packets, and internal
packet density remain explicit hypotheses. The argument does not
extend them to arbitrary sea words.

