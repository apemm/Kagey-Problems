# Independent audit of selected private blocking sets

9 November 2026.

The proposition in private_blocking_set_lower_bound.md is valid with its
stated infinite-strip and universal-completion hypotheses.

For an odd endpoint \(2k+1\), take a positive factor pair \(uv=k^2\),
\(u<v\). The pairs
\[
 \{(0,2k+1),(v-u,1)\},\qquad
 \{(-u,k+1),(v,k+1)\}
\]
have the same midpoint and squared diagonal length, since
\((v-u)^2+4k^2=(u+v)^2\). They define a nondegenerate tilted
rectangle. Its presentation agrees with that of the axis rectangle
on rows \(1,k+1\) and columns \(-u,v\) whenever the three sea columns
\(-u,v-u,v\) have row 1. These columns are distinct and nonzero.
The shared points remain white because \(1<k+1<h\). The second
endpoint of the double at column zero cannot change this collision.

Consequently, every private prescription that works under every
remaining binary filling must prescribe row \(h\) on a hitting set
of these triples. A negative column determines \(u\); a positive
column occurs at most once as \(v\), and at most once as \(v-u\),
because \(u(u+x)=k^2\) has at most one positive solution. The
maximum incidence degree is two. The resulting lower bound
\((\tau(k^2)-1)/4\) on the number of high pins is therefore correct.

The divisor average is also self-contained. The identities
\(\tau(k^2)=\sum_{d\mid k}2^{\omega(d)}\) and
\(2^{\omega(d)}=\#\{(u,v):uv=d,\gcd(u,v)=1\}\) are exact.
Restricting to \(u,v\le\sqrt X\) and subtracting the union bound
for common divisors leaves a positive fraction of the harmonic
square, since \(\sum_{r\ge2}r^{-2}<1\).
Thus \(\sum_{k\le X}\tau(k^2)\gg X\log^2 X\).
Each odd row belongs to \(h/2\) parity edges, giving the claimed
\(\Omega(h^2\log^2 h)\) sum over all private sets.

The width conclusion requires the translated selected sets to be
pairwise disjoint and contained in the board. It is a limitation of
that assembly method. It does not apply to prescriptions using the
finite ends, compatible overlaps, or a jointly chosen sea, and it
does not lower-bound the actual equality threshold.
