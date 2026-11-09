# Independent audit of the filled period-seven cover

9 November 2026. The complete theorem in
[Filled period-seven profile cover](filled_mod7_profile_cover.md)
passes an independent audit, including its filled collars.

The normalization preserves dot products and norms: the horizontal
divisor is either \(g\) or \(-g\), and the vertical divisor is \(g\).
Their squared scale factors agree. Since \(-1\) is a nonsquare modulo
seven, one horizontal sign keeps the original character convention.

I recomputed the mixed equations with one inserted residue \(0\) or
\(5\), one filler residue \(3\), and two binary sea points. The only
survivors for residue zero are the two listed cases. Their displayed
white rows are
\[
 H+(r-F)/2,\qquad (r+F-H+L)/2,
\]
respectively, and the bulk inequalities put them outside the ambient
strip. Residue five has no modular survivor. Cases with two or three
fillers are excluded by the stated norm and perpendicularity equations.
The three-black survivors for inserted residue zero have completion
rows \(F+L-r\) and \(r+F-H\), both below the strip.

The explicit row choices work. The high-row interval contains fourteen
candidates in its prescribed residue class modulo fourteen. Each of
the at most thirteen low-overhang square conditions removes at most
one. The filler interval similarly contains 196 candidates, and each
of at most 195 high-overhang conditions removes at most one. At the
specified height the consecutive-square separations exceed the full
candidate interval lengths. These choices give
\(F-L\ge986>2(h-H)\) and all other asserted margins.

The genuinely two-row one-label cases are also covered. Every sea
level is outside the interval between the two inserted rows. A
three-black tilted right angle cannot use both. In mixed supports,
equal-parity sea levels give odd total row sum, while the remaining
two-level choices bracket the central rows and satisfy the previously
audited two-boundary contradiction. The vertical overhang families
in Section 5 include every remaining possibility, with harmless
overcounting.

The collar needs the extra zero-residue high columns, and that
extension is valid. In the low-side mixed calculation a zero high
column can only give central residue \(5\), while the filler is \(3\).
After reflecting both coordinates, a zero low column can only give
central residue \(4\), while the reflected filler is \(5\).
The horizontal-side negative-square product is nonzero, so it cannot
use a newly allowed zero side column. All exterior cases stay exterior.
In particular, the potential triangle completion \(F+H-L\) is above
row \(h\), by the explicit margin choice.

Thus each hole may choose \(F\) or \(H\) independently during the
collar. The subsequent arbitrary binary \(L,H\) region is valid by
opposite physical parity and the vertical-square filters. The stated
buffers prevent a local support from touching both a retained filler
and the later changed binary region. Adjacent-row parity bridges
then join constant \(H\) to constant \(h\), with only constantly many
switches.

The 84 profiles cover every residue pair, and their exceptional row
union is \(O(\sqrt h)\). Treating those labels separately with the
uniform positional theorem costs \(O(h^2)\), including collars.
The cover removes private sea-prescription conflicts. It still
requires a separate multi-label placement theorem.
