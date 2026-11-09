# Third review of the safe-triangle placement bound

9 November 2026. The proof in [safe_triangle_pair_first_moment.md](safe_triangle_pair_first_moment.md) passes this independent review. The resulting statement is the all-height upper bound
\[
 m_0(h)\ll_\varepsilon h^2(1+\log h)^{2+\varepsilon}.
\]
The review covers the safe-triangle completeness, restricted weighted pair estimate, restored six-cell events, and placement sum. It does not establish a constant-times-quadratic threshold.

## 1. Retained triangles and collision completeness

After normalization, the sea levels are \(0,3,1\) and the inserted endpoint residues are \(0,5\). At a low root, the products of endpoint offsets are zero or four, so the modular right-angle equation has no nonzero solution. At a filler root both horizontal offsets vanish while the vertical product does not. At a high root, equal endpoint residues require a nonsquare; mixed residues require the high column to be 2.

Thus the only sea-rooted tilted triangles use a high corner and two distinct labels, one odd residue-zero endpoint and one even residue-five endpoint. Their completion has column residue 5 and row residue 4. It is a low-sea column, is always white, and has the same physical parity as the low sea point in that column. Its singleton therefore has no final-parity axis rival.

For two triangles on the same two labels, equality of completion columns fixes the high sea point. Equality of completion rows and right-angle products fixes the unordered pair of selected label rows. The two alternative cross choices then imply that the unordered labels coincide. This excludes a genuine two-label six-cell collision.

Any other shared-white collision either has another shared black corner, giving a four-cell symmetric difference, or has six distinct nonshared black cells. The latter uses three or four labels and is explicitly restored. A hidden tilted rectangle cannot contain a retained triangle, because that triangle's completion is white. The remaining hidden and axis cases are covered by the existing positive-support classification and uniqueness of parity labels.

## 2. Arithmetic input and uniformity

I checked [Henriot, Corollary 2](https://arxiv.org/pdf/1102.1643) directly. The [2014 erratum](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B0BD208D979495FE06B8192209E710EA/S0305004114000280a.pdf/nairtenenbaum_uniform_with_respect_to_the_discriminanterratum.pdf) retains the required upper bound.

For distinct primitive affine factors, the ordinary-prime contributions are \(2^s-1\) from \(\tau^s\), two from \(\tau(n^2)\), and one from each ordinary divisor factor. These give the exponents in the three estimates (7). The exceptional primes divide bounded leading coefficients or nonzero resultants of size \(h^{O(1)}\). Their contribution is at most a fixed power of \(1+\log\log(3h)\). Absolute values and deletion of zero values match the theorem's use. The polynomial size after translating the summation interval is \(O(h^3)\), so the stated fixed size parameter is valid.

## 3. Restricted pair roles

The role table is exhaustive after exchanging endpoints and the two labels.

For a three-black triangle rooted at a label, one factor is private and bounded by its class weight. The other factor has a bulk root, distinct from every sea-rooted class-weight factor. Sea-rooted angles are exactly the safe triangles already retained.

Vertical rivals and horizontal mixed sides give a squared row difference. Its varying bulk root is distinct from the private roots. A horizontal side using label and sea points is impossible because their row ranges are disjoint. Equal-row label sides leave only \(O(h)\) partner labels; the maximum-divisor bound absorbs these slices.

For nonhorizontal mixed sides, the factors are the side row difference and the black-pair row-sum difference. The checks that prevent an extra logarithm are valid:

- The identities \(a-b=s-t\) and \(a+b=s+t\) are excluded by physical parity, the bulk margins, and the two separate residue block types.
- The exceptional sea combination \(a=s+t-u\) has been deleted.
- The apparent coincidence \(2a=b+s\) in the second table row is geometrically impossible. The displayed equations force both \(z(z-x)>0\) and \(z(z-x)\le0\).
- The third table row has only finitely many conditioned endpoint slices with coincident roots. Every such slice has \(O(h)\) labels and contributes \(h^{1+o(1)}\).
- Four distinct support cells confined to two double columns force either a repeated black point or repeated unordered label.
- A high/low sea side has only \(O(1)\) vertical translates in the strip. Its row-sum condition fixes one endpoint of the second label, leaving \(O(h)\) labels.

For a class-weight factor on one endpoint, averaging a geometric factor first in the other endpoint is legitimate. Where two geometric factors share the averaging variable, their roots are distinct after the stated exclusions. This gives the claimed
\[
 Q\ell^{C_d}(\Lambda^2+w\Lambda)M(w)+h^{1+o(1)}
\]
restricted incident first moment.

## 4. Six-cell restoration and the positional local lemma

A genuine restored collision contains two high sea corners and four distinct label cells. The equality of completion rows is a nontrivial equation in the free endpoint variables, even if one label supplies both of its endpoints. Fixing one label therefore leaves \(O(Q^{k-1}/h)\) row assignments for \(k=3,4\).

For each assignment, the two right-angle product equations have only \(h^{o(1)}\) factorization choices. Aligning the common completion fixes their relative translation. Squaring this count remains \(h^{o(1)}\), so the row-equation saving absorbs the restored family into the existing higher-arity estimate.

With
\[
 N\ge C\bigl(B(w)+\sqrt{nQ}\sqrt{A(w)}+n+1\bigr),
\]
the pair contribution is \(O(B(w)/N)\). The three-label and four-label contributions are bounded by
\[
 O(nQA/N^2),\qquad
 O((nQ)^{3/2}A/N^3),
\]
respectively. The latter is no larger because \(A\ge1\). Center coincidences cost \(O(n/N)\). Each event has at most four independent label-center variables, so the product-form local lemma applies after increasing the absolute C.

The two weighted class tails sum to an exponent tending to one for \(\sum wM(w)\). The resulting pair width and the higher-arity width are both \(O_\varepsilon(Q\Lambda^{2+\varepsilon})\). The filled collars cost \(O(h^2\log h)\), and the exceptional labels cost \(O(h^2)\), both smaller than the claimed total.

No omitted two-label singleton collision or unaccounted private-private arithmetic factor was found.

