# Independent audit of the fourth-logarithm threshold

9 November 2026. The proof in compatible_profile_threshold.md passes
independent review. Together with the separately checked filled
modulo-seven profiles, it gives the unconditional bound
\[
 m_0(h)\ll_\varepsilon h^2(1+\log h)^{4+\varepsilon}
 \qquad(\varepsilon>0).
\]
This is a construction of complete identifying boards, including
singleton columns and finite ends. It is not just a double-column
scaffold. An absolute quadratic threshold remains unproved.

The profile input is reviewed in filled_mod7_independent_audit.md.
This note checks the arithmetic refinement and placement argument.

## 1. Arithmetic input and the smaller weight

The two-factor moment is the same discriminant-uniform estimate
already reviewed in sharper_polylogarithmic_threshold_independent_audit.md.
For nonconstant affine forms of bounded coefficients, the normalized
second moment of their product's divisor function is
\(O(\Lambda^8\ell^C)\), uniformly in constant terms of size \(O(h)\).
Distinct primitive factors have the smaller exponent six; repeated
factors give eight. Bounded contents do not introduce an additional
row-dependent weight.

The source is [Henriot's uniform upper bound](https://arxiv.org/pdf/1102.1643),
with the corrected exceptional-prime parameter in the
[2014 erratum](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B0BD208D979495FE06B8192209E710EA/S0305004114000280a.pdf/nairtenenbaum_uniform_with_respect_to_the_discriminanterratum.pdf).
Translating the summation interval makes its scale \(h\), while the
quadratic polynomial has height \(O(h^2)\). The theorem's size condition
therefore holds with a fixed exponent below \(1/2\). The exceptional
prime product costs only a fixed power of \(\ell\).

For the new weight
\[
 v(e)=1+\sum_{r\in e,\ s\in\{L,F,H\}}\tau(|r-s|),
\]
the bulk separation ensures that all arguments are nonzero. Each
endpoint has \(O(h)\) possible partners. Applying the single-form
moment and a fixed finite-sum inequality gives
\[
 \sum_e v(e)^s\ll_s Q\Lambda^{2^s-1}
\]
for fixed \(s\) near two, and \(\sum_e v(e)\ll Q\Lambda\).
The sea levels may depend on \(h\); translating a difference still
leaves an interval of length \(O(h)\).

## 2. Fixed-label geometry

Condition on a label \(e\). In a three-corner right angle the divisor
product consists of the two vertical leg differences. In a nonvertical,
nonhorizontal mixed support it consists of the side's row difference
and the difference of the two black-pair row sums. Each support has
only constantly many choices of roles and selected endpoints.

If both factors vary in the other label endpoints, the two-form
moment applies, including dependent or repeated forms. If exactly
one factor is fixed, its nonconstant part is a difference between
an endpoint of \(e\) and a sea row, so it is bounded by \(v(e)\).
The varying factor has second moment \(O(\Lambda^3)\).

There are two useful checks on this statement. A right-angle role
cannot have a leg joining both endpoints of \(e\): that leg would
be vertical, and its perpendicular leg horizontal, producing an
axis-aligned rectangle. A mixed side joining the two endpoints of
\(e\) is likewise the vertical-side case, which is treated as a
vertical parity rival. Thus an unweighted fixed factor
\(\tau(|a-b|)\), for \(e=\{a,b\}\), does not survive in the ordinary
nonvertical product count.

A different label's two endpoint rows remain two variables when
averaging over the full edge family. Using the same endpoint twice
would repeat the same black point and is inadmissible. Numerical
equalities between rows of different labels are restrictions on this
row box, not symbolic cancellations of its variables.

## 3. Exceptional roles

The separate cases in Section 3 of the main note are complete.

* A side on \(L,F\) has bounded vertical difference. A side on \(L,H\)
  or \(F,H\) can translate vertically by only \(O(1)\) values, because
  it already spans \(h-O(1)\) rows. Its diagonal row sum is then fixed.
  A support using at least two labels has both diagonal points on
  different labels. Fixing \(e\)'s selected endpoint leaves \(O(h)\)
  choices for the other label. The uniform subpower divisor bound
  makes the total squared contribution \(O(h^{1+o(1)})=O(Q)\).

* For a horizontal mixed side the count is
  \(O(\tau(d^2))\), where \(d\ne0\) is the diagonal row difference.
  If \(d\) varies, its squared mean is \(O(\Lambda^8)\).
  This also follows directly from
  \(\tau(n^2)^2\le d_9(n)\).

* If that diagonal joins an endpoint of \(e\) to a sea point, both
  horizontal-side endpoints must belong to other labels: bulk label
  rows cannot equal a sea row. The side endpoints have equal rows,
  losing one free row parameter. Moreover, neither can belong to
  \(e\). Equal length and nonzero diagonal row difference put both
  diagonal endpoint columns strictly inside the side's endpoint
  columns. The lost parameter absorbs the fixed subpower divisor
  factor after squaring.

* A diagonal on \(L,H\) or \(F,H\), or on the two endpoints of one
  parity label, has odd row sum and cannot share an integral midpoint
  row with a horizontal side. A diagonal on \(L,F\) has bounded
  difference. Equal-row alternatives are degenerate in this role.

* A vertical parity rival involving two labels has a row difference
  varying in the second label. Equal-row black diagonals give
  same-parity displayed rows and are harmless. A vertical black
  diagonal inside one double column has no distinct vertical
  alternative.

These cases prove, for \(k=2,3,4\),
\[
 \sum_{J\ni e,\ |J|=k}G_J^2
 \ll Q^{k-1}\bigl(\Lambda^8\ell^C+v(e)^2\Lambda^3\bigr).
\]
In the horizontal exceptional case the missing row parameter is
important: applying a uniform divisor bound without that loss would
not prove this estimate.

## 4. Placement and complete validity

For a dyadic class of \(n\) labels and upper weight \(w\), Cauchy--Schwarz
gives the claimed incident geometry sum. A fixed translated geometry
on \(k\) distinct label centers has probability at most \(N^{-(k-1)}\):
one center determines the other \(k-1\) positions. Restricting centers
to period-zero slots can only reduce this probability.

With
\[
 N=C_0\sqrt{nQ}\bigl(\Lambda^4\ell^C+w\Lambda^{3/2}\bigr),
\]
the sum of twice the event probabilities incident to a variable is
at most \(1/8\), after increasing \(C_0\). Coincidence events satisfy
the same bound. Events use at most four centers, so the product-form
local lemma applies.

No private prescription or influence-disjointness condition is used.
The background theorem handles supports with zero or one assigned
label. The positional events handle every support with two or more.
Three-black tilted rectangles are excluded, so hidden rectangles and
six-black singleton collisions are excluded as well. The remaining
tilt/tilt and oblique or horizontal axis rivals reduce to the mixed
four-point family; vertical axis rivals are explicitly included.
Unique parity edges give the global axis/axis condition.

The fixed profile bridges and collars are essential to the conclusion:
they supply finite ends and allow concatenation of classes while
retaining the full final parity graph for distant axis rivals.

## 5. Summing the classes

The first moment gives
\[
 \sum_j\sqrt{n_j}\ll\sqrt{Q(1+\log\Lambda)}.
\]
For the weighted sum, let
\(A_\pm=\sum_j n_jw_j^{2\pm d}\), with fixed small \(d>0\).
Splitting the dyadic sum at \(W\) yields
\[
 \sum_jw_j\sqrt{n_j}
 \ll_d \sqrt{A_-}W^{d/2}+\sqrt{A_+}W^{-d/2}
 \ll_d(A_-A_+)^{1/4}.
\]
The resulting logarithmic exponent tends to \(3/2\) as \(d\) tends
to zero. No factor equal to the number of classes is introduced.
Consequently the total internal width is
\[
 O_\varepsilon\!\left(Q\Lambda^{4+\varepsilon}\right).
\]
There are only \(O(\log h)\) classes, so their \(O(h^2)\) collars
cost \(O(h^2\log h)\). The exceptional \(O(h^{3/2})\) labels use the
previous uniform positional lemma and cost \(O(h^2)\), including
their bounded number of background collars. Constant boundary tails
provide every larger width.

The conclusion in the main note can therefore be stated
unconditionally, citing the completed profile audit.
