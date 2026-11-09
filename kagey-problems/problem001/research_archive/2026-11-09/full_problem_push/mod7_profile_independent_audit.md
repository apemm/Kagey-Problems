# Independent audit of punctured binary profile compatibility

9 November 2026. The proofs in
[Binary-boundary one-label separability](binary_boundary_one_label_separability.md)
and [The eighteen-profile cover](mod7_inset_profile_cover.md) pass an
independent audit.

The separability argument accounts for actual symmetric-difference
supports. A tilted right angle cannot use both central rows when every
other black point lies on a boundary outside their interval. With one
central row, the completion row and the sum and product of the two sea
columns determine the singleton presentation uniquely. Opposite central
rows therefore cannot create a six-cell singleton collision.

For a mixed four-cell support using both central rows, equal sea rows
give odd total row sum. Opposite sea rows either contradict the diagonal
length comparison, or lead to the displayed equations (3). In their
nonzero case, the equal-norm identity gives
\[
 x(z-x)<\alpha(\alpha-\beta),
\]
while orthogonality requires the opposite inequality. The zero cases
are degenerate. This proof also applies to central rows strictly between
inset sea rows; it does not require those sea rows to be the ambient
strip boundaries.

The modulo-seven one-point calculation is correct. The character
condition makes the right-angle product a nonzero square, whereas the
two opposite sea characters have nonsquare product. In the remaining
mixed case the only residue pairs are \((2,3),(4,5),(4,6)\);
their values of \(d-2c\) are \(6,5,0\), respectively, all incompatible
with \(u^2(d-2c)=c^2\ne0\).

The outer-strip checks are necessary and sufficient in the stated
central row range. For \(125\le r\le h-124\), one has
\(r-L\ge122\) and \(H-r\ge83\). Each exceeds twice either relevant
outer margin. All formerly out-of-strip three-corner cases and
nonvertical mixed cases still leave the ambient strip. The only
new one-label possibilities are the central/sea vertical alternatives,
with exactly the two square equations listed in the note.

The zero-label condition also passes. The three candidate high rows
are spaced fourteen apart. Above the stated minimum span, each of the
two bad square sequences excludes at most one candidate. Same-row
vertical alternatives have same-parity white endpoints; opposite-row
alternatives are exactly the excluded \(j(G+j)\) squares. The
zero-label mixed cases are either ruled out by row parity or
degenerate.

Finally, \(T/T=\mathbb F_7^*\), so choosing one of three low-row
residues and one of six nonzero spans covers every remaining pair.
The union of exceptional rows has size \(O(\sqrt h)\). Their labels
can be treated by the already proved positional construction with
only a constant number of background blocks and collars. This does
not solve the simultaneous placement or unused-hole filling problem
in the eighteen new profiles.
