# Continuation: separable canonical CRT placements have an unavoidable P collision

9 November 2026. The apparent quadratic-width candidate in [continuation_power_two_filler_coupling.md](continuation_power_two_filler_coupling.md) has a structural obstruction. The result below allows an arbitrary injection F, not just a two-adic isometry. It also survives splitting labels by their odd row modulo four.

## 1. Statement and scope

Fix one odd residue \(r\bmod4\). Retain every label
\[
 \{a,b\},\qquad a\equiv r\pmod4,\quad a\text{ odd},\quad b\text{ even},
 \quad 1\le a,b\le h.
\]
Choose coprime p,N with \(p>10h\), and an injection
\[
 F:\{0,\ldots,\lfloor h/2\rfloor-1\}\longrightarrow\{0,\ldots,N-1\}.
\]
Place the label \(\{2i+1,2j+2\}\) at the canonical column
\[
 x_{ij}=4z_{ij},\qquad
 z_{ij}\equiv i\pmod p,\quad z_{ij}\equiv F(j)\pmod N,\quad
 0\le z_{ij}<pN.                                           \tag{1}
\]

For sufficiently large h, avoiding all vertical tilted/axis collisions in this placement requires
\[
 N\ge c h^{3/2}.                                           \tag{2}
\]
In particular, \(N=O(h)\) is impossible. The actual occupied span is then at least of order \(h^{5/2}\): for any fixed even row, there are \(\Theta(h)\) retained odd endpoints, their distinct centers are all congruent modulo \(4N\), and their span is therefore \(\Omega(hN)\).

The canonical-representative hypothesis is essential to this statement. It does not cover choosing different multiples of pN independently for different labels, or arbitrary nonseparable column rules. Bounded lifts depending only on the even row j can be treated by applying the same pigeonhole argument in a common even-row lift class. Lifts depending on the odd row or on the full label require another argument.

## 2. A close pair of even-row images

Let
\[
 D=\lfloor\sqrt h/10\rfloor
\]
and restrict to even rows in \([h/3,2h/3]\). There are
\(M\ge h/6-O(1)\) such rows.

If no two corresponding F-images of the same parity have positive ordinary difference at most D, each of the two parity classes is D-separated in \([0,N)\). Hence
\[
 M\le2+2N/D.
\]
Therefore \(N<c h^{3/2}\), for a sufficiently small absolute c, supplies two central even rows
\[
 b_1=2j_1+2,\quad b_2=2j_2+2
\]
whose ordinary representatives satisfy
\[
 F(j_2)-F(j_1)=d,\qquad 2\le d\le D,\quad d\text{ even}.       \tag{3}
\]

Put \(b=b_2\) and \(v=4d^2-1\). Of the two choices
\[
 a=b-v,\qquad a=b+v,
\]
exactly one has the required residue r modulo four. Both choices, and \(a+2d\), lie in the strip for large h because b is central and \(v\le h/25\). Thus both labels
\[
 e_1=\{a,b_1\},\qquad e_2=\{a+2d,b\}                         \tag{4}
\]
belong to the retained mod-four family.

## 3. The CRT representatives have the actual short gap

Their odd indices differ by d, and (3) gives the same difference modulo N. Consequently
\[
 z_2-z_1\equiv d\pmod{pN}.
\]
The canonical representatives permit only d or \(d-pN\).

The second value would require \(z_1\ge pN-d\), hence
\(F(j_1)\ge N-d\). But (3) is an ordinary positive difference, so
\[
 F(j_2)=F(j_1)+d<N,
\]
a contradiction. Therefore
\[
 x_2-x_1=4d.                                               \tag{5}
\]

This ordinary-representative argument avoids any probabilistic or sign-based wrap assumption.

## 4. An immutable collision inside the same residue family

Choose the odd black point A at row a in the first label and the even black point B at row b in the second. Their vertical difference has absolute value v, and
\[
 (4d)^2+(4d^2-1)^2=(4d^2+1)^2.
\]
Thus they are opposite corners of an integral tilted rectangle whose other diagonal is vertical. Its two white candidate rows are
\[
 \min(a,b)-1,\qquad \max(a,b)+1.
\]
They lie in the strip and have opposite parity.

The odd one is
\[
 u=a+4d^2\quad\text{or}\quad u=a-4d^2.
\]
In either case \(u\equiv a\equiv r\pmod4\). Hence the double label consisting of these two displayed rows is present in the same mod-four family.

Its owner column cannot be the common midpoint column. The midpoint has CRT odd residue
\[
 i_a+d/2\pmod p,
\]
whereas the owner label has odd residue
\[
 i_a\pm2d^2\pmod p.
\]
Their difference is nonzero and has absolute value less than p. The owner column is also distinct from the two original label columns, by the analogous differences \(\pm2d^2\) and \(\pm2d^2-d\).

The axis rectangle formed by the vertical displayed pair and its owner label has exactly the same presentation as the tilted rectangle. Their symmetric difference consists of A, B, and the two owner points, all already black. Later filling cannot repair the collision, regardless of the colors eventually assigned to the two shared points.

This proves (2).

## 5. Consequence for filler coupling

The large singleton alphabets in the preceding note correctly neutralize a substantial class of two-double triangles. They cannot repair this P collision, which is already forced by the inserted double columns.

Therefore the separable canonical CRT family with \(N=O(h)\) is not a viable complete quadratic-width construction, even after the two odd-residue groups are placed separately. A successful continuation must change the placement rule, introduce genuinely label-dependent lifts with a controlled coloring theorem, or abandon a single global even-row map F.

The right-angle and filler lemmas remain valid partial statements. They no longer support treating this particular canonical family as a candidate for a full quadratic-width board.

Independent review passed. See [separable_crt_spacing_independent_audit.md](separable_crt_spacing_independent_audit.md).



## 6. Reproducible exact certificates

[verify_separable_crt_p_obstruction.py](verify_separable_crt_p_obstruction.py) checks heights 4096, 16384, and 65536. At each height it uses an identity map, a seeded random injection, and a seeded nonaffine dyadic isometry. It produces both retained odd-residue cases, for 18 exact collisions.

The checker computes black membership from the inverse residues of the full label family. It does not enumerate the \(\Theta(h^2)\) labels. Each certificate checks both rectangles, their equal presentations, the distinct axis owner, and the four already-black symmetric-difference cells. Seeds, parameters, map SHA-256 hashes, and exact coordinates are recorded in [verify_separable_crt_p_obstruction.json](verify_separable_crt_p_obstruction.json).

All 18 checks pass. The independently written audit also checks eight certificates with other maps at height 10000.



## 7. Any fixed finite-residue row split has the same obstruction

Fix an even integer M, an odd residue r, and an even residue beta modulo M. Retain every label
\[
 a\equiv r\pmod M,\qquad b\equiv\beta\pmod M,\qquad 1\le a,b\le h.
\]
Allow an arbitrary injective F on these even-row indices, and use the same canonical CRT rule (1). Then
\[
 N=\Omega_M(h^{3/2}),\qquad
 \text{occupied width}=\Omega_M(h^{5/2})                     \tag{6}
\]
is necessary to avoid P collisions.

Choose a positive odd integer k representing \(r-\beta\pmod M\), and put \(T=2Mk\). Among the \(\Theta_M(h)\) central even rows in the beta class, pigeonhole the ordinary F-images according to their residues modulo T. Unless \(N\ge c_Mh^{3/2}\), two such images have positive gap
\[
 d\equiv0\pmod{2Mk},\qquad 0<d\le\sqrt h/10.
\]
Use the integer Pythagorean triple
\[
 (4d)^2+\left(\frac{4d^2}{k}-k\right)^2
       =\left(\frac{4d^2}{k}+k\right)^2.                     \tag{7}
\]
Set \(b=b_2\), \(v=4d^2/k-k\), and \(a=b-v\). Since M,k are fixed, all selected and completion rows lie in the strip for large h. Moreover,
\[
 a\equiv r,\qquad a+2d\equiv r\pmod M.
\]
The source labels \(\{a,b_1\}\) and \(\{a+2d,b_2\}\) are retained. Their actual column gap is 4d by the same ordinary-representative no-wrap argument.

The displayed vertical pair has rows
\[
 b-\frac{4d^2}{k},\qquad b+k.                               \tag{8}
\]
The first is even and remains in the beta class; the second is odd and remains in the r class. Thus its double owner belongs to this very same residue-pair family.

The owner's odd index differs from the midpoint's odd residue by
\[
 \frac{2d^2}{k}-\frac d2
       =\frac{d(4d-k)}{2k},
\]
which is nonzero and smaller than p. The same strict inequalities separate it from the original two owner columns. The tilted and axis rectangles therefore give the same immutable collision as before.

For one fixed even row there are \(\Theta_M(h)\) retained odd endpoints, with distinct centers congruent modulo 4N. This proves the actual width lower bound in (6).

The constants may depend on M. Consequently a bounded finite-residue split cannot rescue the canonical separable CRT template when one component retains the full indicated residue-pair Cartesian family. Full retention is essential: this does not rule out deleting or reassigning exceptional labels, a non-residue subdivision before choosing F, arbitrary label-dependent lifts, or nonseparable placement.

