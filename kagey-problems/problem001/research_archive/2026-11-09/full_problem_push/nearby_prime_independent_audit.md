# Independent audit of the nearby-prime scaffold

9 November 2026. The geometric and arithmetic reductions in
[Nearby-prime scaffold](nearby_prime_scaffold.md) pass an independent audit.
The conclusion concerns the empty scaffold; it does not certify its
remaining P and mixed conditions or complete its singleton columns.

The prime input has the required interval strength. The weighted sum in
Maynard's proof of Proposition 4.2 is over \(N\le n<2N\), and equation
(4.4) is positive for every sufficiently large \(N\). Together with
\(M_{105}>4\), this supplies a bounded-gap pair in every sufficiently
large dyadic interval, with a fixed additive enlargement. A fixed
admissible tuple of 105 primes greater than 105 is sufficient.
[Primary source, pp. 388–390](https://annals.math.princeton.edu/wp-content/uploads/annals-v181-n1-p07-p.pdf).

The modular right-angle proof is valid at both endpoint parities.
The mixed bracket is an odd, nonzero integer of absolute value less
than the relevant prime. The placement is injective, and all its
horizontal differences are multiples of four.

For a cross-block mixed side, the norm estimate forces equality of
the two offset differences, while perpendicularity forces equality
of the offset sums. This correctly matches the two blocks. The
subsequent cases exhaust the even number of matched parity changes:
zero changes, two opposite changes, or two changes in the same
direction. In the last case the nonhorizontal modular argument
and the separately treated horizontal norm equation both exclude
the collision. The horizontal estimate follows from
\[
 8D\alpha U_x=4K\alpha^2\pm4\alpha w+w^2
\]
and the nonzero even integers \(\alpha,w\).

The within-block reduction can be made explicit as follows.
If a monochromatic side has vector \(d(2D,1)\), let
\(\epsilon,\eta\in\{0,1\}\) record whether its points and the
diagonal's points, respectively, are even. Orthogonality gives
\[
 KS+8Dp(v-u)-2\eta v+2\epsilon u=0.
\]
The large-prime bound forces \(v=u\). Equal norms then make the
two monochromatic vectors parallel, which is degenerate for the
diagonal rectangle.

For two mixed pairs, direct substitution gives precisely
\[
 (Kd+u)S=(d+u-8Dpd)(v-u).
\]
Writing the integral perpendicular connector with
\(g=\gcd(2Dd,d+u)\) gives
\[
 (Kd+u)t=-g(p+q)(v-u).
\]
Here \(g\) is odd and \(|t|\le h-1\). The endpoints of a block
have an odd-index interval of length \(h-1-|u|\), so
\[
 |Kd+u|\le K(h-1-|u|)+|u|<Kh.
\]
This verifies the stated sufficient condition involving a prime
factor of \(p+q\) larger than \(Kh\), without asserting the existence
of that additional prime factor.
