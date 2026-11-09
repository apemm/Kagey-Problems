# Independent audit of the second-logarithm threshold

9 November 2026. The complete proof in
safe_triangle_pair_first_moment.md passes independent review. Combined
with the independently checked filled modulo-seven profiles, it gives
\[
 m_0(h)\ll_\varepsilon h^2(1+\log h)^{2+\varepsilon}
 \qquad(\varepsilon>0).
\]
The conclusion concerns complete identifying boards and all larger
widths. An absolute quadratic threshold remains open.

## 1. The retained triangles are safe

The orientation \(L,F\) odd and \(H\) even is available for every
label: each residue modulo seven has exactly one odd representative
in \([1,14]\). Separating the all-zero and mixed-residue labels
uses only a bounded number of profiles.

For two label corners and a sea-rooted right angle, the modulo-seven
equation has no solution at \(L\) or \(F\). At \(H\), the only
possibility has one label row of normalized residue zero and one
of residue five. The high corner's normalized column is two.
The fourth corner therefore has column residue five and row
residue four. It is white, lies over the low sea row, and has the
same physical parity as that row. It has no singleton axis rival
under the full final parity graph.

Two allowed triangles on the same two labels cannot have the same
completion. Equality of completion columns fixes their common high
corner. Equality of completion rows and right-angle products then
fixes the unordered pair of selected label rows. The only alternative
would make the two unordered labels identical, which is excluded.

If two allowed triangles share another black point, their symmetric
difference is a four-point support. The usual four-support reduction
still applies: same-side or same-diagonal cases would give a hidden
black rectangle; the remaining case is mixed. A hidden tilted
rectangle cannot occur, since an allowed triangle has a forced white
completion and every other three-black triangle is forbidden.

Thus the only restored singleton collisions with six distinct black
points use three or four labels, as claimed.

## 2. Root coincidences in the pair table

The pair-role table exhausts the nonvertical, nonhorizontal mixed
case. A side using both endpoints of one label is vertical and
belongs to the separate parity-rival case. Repeated occurrences
of an endpoint would repeat the same physical point.

The identities removed by the exceptional row set and by parity
are sufficient. A bulk endpoint cannot equal \(s+t-u\) for sea
rows \(s,t,u\). The difference of two label endpoints cannot
equal a sea difference: low/low differences are even, while
high/low differences exceed the difference of two bulk rows.
The label row sum cannot equal a sea row sum, by the normalized
residue calculation and physical parity in the all-zero case.

The one additional possible repeated factor is
\(2a=b+s\) in the role
\[
 A=(0,a),\quad B=(x,c),\quad
 C=(0,b),\quad D=(z,s).
\]
Writing \(y=c-a\ne0\), perpendicularity and equal norm give
\[
 x(z-x)=y^2,\qquad
 x^2+y^2=z^2+(s-b)^2.
\]
The first identity makes \(x,z,z-x\) have the same sign.
The second then gives
\[
 z(z-x)=-(s-b)^2\le0,
\]
a contradiction. This is a geometric exclusion, not an assumed
arithmetic cancellation.

For the role with side \(a,c\) and diagonal \(d,s\), conditioning
on \(d\) leaves only the finitely many exceptional slices
\(d=2a-s\) and \(d=a+u-s\), for sea rows \(u\). Each slice has
only \(O(h)\) labels. Its maximum-divisor contribution is
\(h^{1+o(1)}\), uniformly in the conditioned label.

The four-point role using all endpoints of two labels is impossible:
the pair centers differ vertically, and the equal-norm and
perpendicularity identities force repeated endpoints or the same
unordered edge.

In every remaining ordinary role, extracting the single private
factor by \(v(e),v(f)\le w\) leaves a nonprivate factor. If it
depends on both endpoints of the other label, average first in
the endpoint not used by the class-weight term. The high/low sea
side and equal-row horizontal side each lose one free row parameter
and contribute only the stated uniform subpower remainder.

## 3. The weighted arithmetic estimate

The weighted use of Henriot's upper bound is consistent with its
multivariable arithmetic-function formulation. For distinct primitive
roots, the ordinary-prime coefficients are
\[
 (2^s-1)+(3-1)=\beta(s)+2
\]
for \(\tau(C)^s\tau(A^2)\), and
\[
 (2^s-1)+(2-1)+(2-1)=\beta(s)+2
\]
for \(\tau(C)^s\tau(A)\tau(B)\).
One geometric linear factor gives \(\beta(s)+1\).
The factors are distinct exactly where the proof invokes these
estimates; the role checks above remove every coincidence.

The bounded coefficients and polynomial-size resultants give only
a fixed power of \(1+\log\log(3h)\) from exceptional primes.
Polynomial height \(O(h^3)\) permits a fixed size exponent below
\(1/3\). The arithmetic functions are submultiplicative and satisfy
the required subpower growth. The same corrected upper-bound input
was checked in sharper_polylogarithmic_threshold_independent_audit.md.

Dyadic membership is bounded by
\[
 C_s w^{-s}\sum_{r\in f,\ u\in S}\tau(|r-u|)^s.
\]
Applying each of the three fixed exponents near one, and also the
unweighted bound, therefore gives the minimum \(M(w)\) in the
main note. The exceptional slices are kept outside this minimum,
which is necessary for the asserted uniformity.

Consequently the restricted pair bound is
\[
 \sum_{f\in\mathcal C_w\setminus\{e\}}G_{e,f}
 \ll Q\ell^C(\Lambda^2+w\Lambda)M(w)+h^{1+o(1)}.
\]
The formerly problematic private-private product was the
sea-rooted three-black angle. Its possible instances are exactly
the safe triangles retained above.

## 4. Restored six-point collisions

Each genuine six-point collision consists of two allowed high-root
triangles. Their four label cells are distinct, and the common
completion imposes
\[
 r_1+r_2=r_3+r_4.
\]
With three or four labels and one label fixed, this is a nontrivial
equation in a remaining endpoint. Using both endpoints of one
label does not cancel that variable: they are different endpoint
variables with opposite signs or belong to separate sides of the
equation. Thus the row-assignment count loses a factor \(h\).

For fixed rows, each triangle has only divisor-many horizontal
factorizations. Aligning the white completion fixes their relative
translations. Shared-label column equalities are additional filters
and can be ignored in an upper bound. The summed squared count is
therefore \(O(Q^{k-1}h^{-1+o(1)})\), for \(k=3,4\).
There is no missing arity-two six-point family, by Section 1.

This count is smaller than the already proved higher-arity second
moment. Restoring these events does not change the required
class width.

## 5. Local lemma, width, and ends

For a class of size \(n\), the choice
\[
 N=C\bigl(B(w)+\sqrt{nQ}\sqrt{A(w)}+n+1\bigr)
\]
controls pairs by \(B(w)/N\), triples by
\(nQA(w)/N^2\), and four-label events by
\((nQ)^{3/2}A(w)/N^3\). The last ratio is bounded because
\(A(w)\ge1\). A six-point collision still depends on at most
four center variables. Coincident centers are separately excluded.

The pair sum satisfies
\[
 \sum_jM(w_j)\ll1+\log\Lambda,\qquad
 \sum_jw_jM(w_j)\ll_d
       \Lambda^{2\cosh(d\log2)-1}.
\]
These are geometric-tail sums, not estimates multiplied by the
number of classes. Taking fixed \(d>0\) sufficiently small absorbs
the iterated-log factor into an arbitrary \(\Lambda^\varepsilon\).
The uniform exceptional slices sum to \(h^{1+o(1)}\).

For higher arity, the first-moment class bound and
\(\sum_jw_jn_j\ll Q\Lambda\) give exactly the two terms in
equation (18) of the main note. The total internal width is
\(O_\varepsilon(Q\Lambda^{2+\varepsilon})\).

The earlier filled profile bridges remain applicable. Labels lie
behind unchanged periodic collars, and the two-rectangle span bound
separates them from altered sea columns and from other blocks.
The full final parity graph still handles distant axis rivals.
There are \(O(\log h)\) class collars, costing \(O(h^2\log h)\);
the exceptional labels cost \(O(h^2)\). Boundary constant tails
give every larger width.

The construction therefore has the complete scope claimed in (1).
