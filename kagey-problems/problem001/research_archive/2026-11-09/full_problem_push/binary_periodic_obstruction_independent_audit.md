# Independent audit of the binary-gap results

9 November 2026. The fixed-gap impossibility proofs, the bounded-period
orientation theorem, and the height-19 eventual construction pass the
following independent checks.

## Fixed period-eight gaps

In `period_eight_binary_sea_impossibility.md`, the first two right-angle
products are \(37t^2\) and \(165t^2\). Their completed rows are even, and
their columns are two modulo four. The displayed point is therefore white
above an odd boundary-row singleton, so the full parity graph supplies the
claimed singleton axis rival.

The horizontal Pythagorean certificates force both odd residue classes to
have one color and residue four to have the other. Their endpoint losses
are smaller than the number of doubles carrying the specified central row.
The final mixed collision has common interior white rows in sea columns;
unknown double partners cannot remove it.

The general classification for \(h\ge11\), \(h=3\pmod4\), also checks. All
four listed products equal \((r-1)(h-r)\), and their completions are in sea
columns. The largest right span is at most \(3h-11\), leaving fewer than
\((h+1)/2\) unusable double slots. The surviving masks are exactly
8, 10, 40, and 42 after fixing the common odd-residue color; horizontal
reflection identifies 10 and 40.

## Arbitrary bounded orientation periods

The inverse-graph induction in `periodic_orientation_impossibility.md` is
valid. For even powers of two n, reduction modulo \(4n\) gives the preceding
graph. The identity
\[
(a+4n)^{-1}=a^{-1}+4n\pmod{8n}
\]
shows that an edge has a lift from either vertex above its source. The odd
residue \(1+2n\) has inverse \(1+6n\), and their coarse indices differ by
\(n/2\). This joins the two lifted components.

For general \(P=2^kR\), the choice \(AR\mid N\) ensures that every quotient
\(N/a\) is divisible by R. Its residue modulo \(2^{k+3}\) is \(a^{-1}\).
Thus all vertices in a fixed residue class modulo \(2^k\) share neighbors,
and the quotient graph is precisely the connected power-of-two graph.

The right-angle constraints can all be imposed at the same row-2 double.
Every positive factorization has \(a+N/a\le N+1\), while row 2 has more
occurrences than the number of slots lacking this margin. This simultaneous
choice is essential and is explicitly justified in the proof.

For the final mixed obstruction, write \(F=u+2T\). Its norm identity follows
directly from
\[
5u^2-4F^2=(u-8T)^2-80T^2=(20T^2-1)^2.
\]
All noncentral black and displayed columns have the required residues, and
the displayed rows are strictly interior. The right span is less than
\(h-1\), so the multiplicity of the central odd row guarantees a fitting
occurrence.

Finally, with odd \(T=C\), one has \(F=1\pmod C\). Both congruences for L
have invertible coefficients and coprime moduli. They imply
\(C\mid(2FL-1)\) and \(2FL-1=1\pmod{2^{k+3}}\), exactly the hypotheses
needed earlier. They also give arbitrarily large heights \(h=3\pmod8\).
The theorem therefore excludes every bounded orientation-period budget,
including unrestricted choices at residues two and six. It does not
exclude arbitrary aperiodic orientations.

## Height-19 construction and its verification

The eventual theorem in `periodic_binary_completions_h15_h19.md` uses a
complete checked parity board followed by 16 transition columns and a
164-column row-2 collar. The nonconstant prefix ends at column 729. A new
tilted/tilted support touching it from beyond column 893 would exceed the
height-19 union-span bound 164. Singleton and vertical axis rivals continue
to use the same full parity pair set, already owned in the first 713 columns.
Horizontal and oblique axis comparisons remain local. The resulting formula
\(f(19,m)=m+90\) for every \(m\ge713\) has the stated unrestricted-sea scope.

The independent verifier completes each black pair both as a diagonal and
as a side. Its integer bounds for positive and negative primitive
perpendicular translations are correct. Omitting horizontal black pairs in
a boundary row is safe: they cannot be diagonals of a tilted rectangle
contained in the strip, and treating them as sides gives only axis
rectangles. All remaining tilted rectangles with at least two black corners
are generated. The four explicit axis-rival tests and the structural parity
pair check cover the omitted axis rectangles. A row-range assertion now
also validates singleton input coordinates.
