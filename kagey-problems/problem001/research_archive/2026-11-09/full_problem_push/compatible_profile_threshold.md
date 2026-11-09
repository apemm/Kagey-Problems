# A fourth-logarithm threshold from compatible periodic profiles

9 November 2026. Compatible period-seven profiles and a refined
positional local lemma give an unconditional threshold with
logarithmic exponent arbitrarily close to four.
The [profile theorem](filled_mod7_profile_cover.md) and the arithmetic,
placement, and finite-end arguments below have passed separate
independent reviews:
[profile audit](filled_mod7_independent_audit.md) and
[placement audit](compatible_profile_threshold_independent_audit.md).

Write \(Q=\lfloor h^2/4\rfloor\),
\(\Lambda=1+\log h\), and \(\ell=1+\log\log(3h)\).

## 1. The profile input

The [filled-profile theorem](filled_mod7_profile_cover.md) supplies an
absolute constant number of periodic singleton seas covering all but
\(O(h^{3/2})\) parity labels. Each profile has the following properties,
with constants independent of \(h\).

* Its period is bounded. Its three possible rows are \(L,F,H\), where
  \(L,F=O(1)\), \(H=h-O(1)\), \(L<F<H\), and \(L,F\) have the same
  physical parity, opposite to \(H\).
* The sea has no three-black tilted rectangle, no mixed four-black
  support, and no vertical rival relative to the full parity graph.
* Every assigned label has both rows in
  \([C,h-C]\), for a sufficiently large absolute constant \(C\),
  and can replace the singleton at any designated period-zero column.
  Such a one-label replacement still has none of the preceding
  positive supports.
* The unmodified periodic sea has fixed bridges of length \(O(h^2)\)
  to a boundary constant on either end. Inserting a constant collar
  of length \(2W_h\) makes these bridges compatible with the interior
  labels.

The modulo-seven profiles have these properties after deleting
finitely many \(O(\sqrt h)\) exceptional row families. Their validity
and collars are proved analytically, with a separate exact modular
checker.

**Theorem.** For every
\(\varepsilon>0\),
\[
 m_0(h)\le C_\varepsilon h^2(1+\log h)^{4+\varepsilon}.
 \tag{1}
\]

The exceptional \(O(h^{3/2})\) labels cost only \(O(h^2)\) additional
width. Indeed the original maximum-divisor positional lemma uses
\(O((n+1)T(h)^2)\) internal columns for any \(n\)-label subfamily,
where \(T(h)=h^{o(1)}\). Apply it to these labels in its at most four
canonical binary backgrounds and add their \(O(h^2)\) collars.

## 2. A smaller row weight

Fix a profile. For a label \(e\), put
\[
 v(e)=1+
 \sum_{\substack{r\in e\\s\in\{L,F,H\}}}\tau(|r-s|).
 \tag{2}
\]
The label rows are separated from the three sea levels, so the
arguments in (2) are nonzero.

For \(s\) in a fixed neighborhood of two,
\[
 \sum_e v(e)^s\le C_s Q\Lambda^{\,2^s-1}.
 \tag{3}
\]
The sum may be taken over all bulk parity labels. Each single endpoint
has \(O(h)\) partners, and its difference from a fixed sea row ranges
over an interval of length \(O(h)\). The standard divisor moment for
one linear form therefore proves (3), uniformly in the sea rows.
In particular,
\[
 \sum_e v(e)\le C Q\Lambda.
 \tag{4}
\]

Unlike the earlier weight, (2) contains neither a private influence-set
size nor a divisor function of a square.

## 3. Squared counts for several labels

Let \(G_J\) count the translated relative geometries of three-black
tilted rectangles, nonvertical mixed four-black supports, and vertical
parity rivals that use exactly the labels in \(J\). Other required
black points must lie in one of the three sea rows. Ignoring the
periodic restrictions gives a valid upper bound.

For every fixed \(e\) and \(k=2,3,4\),
\[
 \sum_{\substack{J\ni e\\|J|=k}}G_J^2
 \le C Q^{k-1}
       \left(\Lambda^8\ell^C+v(e)^2\Lambda^3\right).
 \tag{5}
\]

Here and below, a term for a geometrically impossible role assignment
is zero. There are only constantly many roles and endpoint choices.
The fixed finite-sum square inequality reduces the proof to one role.

For three corners with fixed rows, the horizontal product equals
the product of two nonzero vertical differences. For a nonhorizontal
mixed side with vertical difference \(y\), and black-pair row-sum
difference \(s\), the horizontal side component divides \(ys\).
Thus the relevant count is \(O(\tau(|AB|))\), where \(A,B\) are
affine forms in the row endpoints.

If both forms vary with the other labels, the discriminant-uniform
two-factor second-moment estimate from
[sharper_polylogarithmic_threshold.md](sharper_polylogarithmic_threshold.md)
gives \(O(\Lambda^8\ell^C)\). This bound includes repeated factors.
If exactly one factor is fixed by \(e\) and a sea point, its absolute
value is \(|r-s|\) from (2). The inequality
\(\tau(AB)\le\tau(A)\tau(B)\), followed by the single-form second
moment, gives \(O(v(e)^2\Lambda^3)\).

There is no ordinary role in which both forms are fixed while another
label contributes a free endpoint. In a three-corner product, every
other endpoint occurs in a vertical difference. In a nonhorizontal
mixed product, an endpoint not in the side occurs in the row-sum
factor; an endpoint in the side occurs in its difference or its sum.
The two different rows of one other double remain distinct row
variables. A repeated endpoint of the same double would repeat the
same physical point and is not a permitted support.

The following exceptional roles need separate checks.

**A side joining two sea levels.** The difference \(F-L\) is bounded,
so this fixed factor costs only a constant. A side joining \(H\) to
either low sea level spans \(h-O(1)\) rows. Its perpendicular
translate can move it vertically by only \(O(1)\) integer values
\(j\). The black diagonal therefore has row sum equal to the side's
row sum plus \(2j\). For a support with at least two labels, both
diagonal endpoints are labels. Once \(e\)'s endpoint is fixed, there
are only \(O(h)\) possible other labels. Their divisor count is at
most \(h^{o(1)}\), uniformly, so their total squared contribution is
\(O(h^{1+o(1)})=O(Q)\).

**A horizontal mixed side.** Write \(d\ne0\) for the black diagonal's
vertical difference. Its count is \(O(\tau(d^2))\). If \(d\) varies
with another label, the uniform second moment is
\[
 h^{-1}\sum_{t\le h}\tau((t-c)^2)^2
 \le C\Lambda^8,
 \tag{6}
\]
with harmless parity restrictions.
If the diagonal has one endpoint in \(e\) and the other in a sea row,
then \(d\) is fixed. Both horizontal-side endpoints must be labels:
a side containing a sea point would force a label endpoint into that
same sea row, excluded by the bulk hypothesis. Those two label
endpoints have the same row, losing one free row parameter. Hence
even the uniform subpower bound for \(\tau(d^2)^2\) is absorbed by
that loss.

The fixed label cannot simultaneously supply a diagonal endpoint
and a horizontal-side endpoint. The diagonal has nonzero vertical
difference and the same length as the horizontal side, so both
diagonal endpoint columns lie strictly between the two side endpoint
columns. They cannot coincide with an endpoint column.

If both diagonal endpoints are sea points, the pairs \(L,H\) and
\(F,H\) have odd row sum and cannot give an integral horizontal
presentation. The remaining difference \(F-L\) is bounded.
A diagonal consisting of a double's two endpoints likewise has odd
row sum and is impossible in this horizontal case.

**Vertical parity rivals.** The difference of two label endpoints
varies with the other label, so (6) applies. Equal-row alternatives
have same-parity displayed rows and are harmless. A black pair in
one double column cannot have a distinct vertical alternative.

These cases exhaust the finite geometry factorization and prove (5).

## 4. Placement without private prescriptions

Partition the profile's labels into dyadic classes of (2). In a class
of size \(n\), let \(w\) be its dyadic upper weight. Choose each center
independently among \(N\) period-zero slots. Coincident centers are
forbidden separately. There are no influence-overlap events: the
entire sea is already fixed and each one-label insertion is valid.

Cauchy--Schwarz and (5) give
\[
 \sum_{\substack{J\ni e,\ J\text{ in the class}\\|J|=k}}G_J
 \le C(nQ)^{(k-1)/2}
      \left(\Lambda^4\ell^C+w\Lambda^{3/2}\right).
 \tag{7}
\]
Every translated geometry on \(k\) centers has probability at most
\(N^{-(k-1)}\). Take
\[
 N=\left\lceil C_0\sqrt{nQ}
       \left(\Lambda^4\ell^C+w\Lambda^{3/2}\right)\right\rceil.
 \tag{8}
\]
The sum of twice the bad-event probability bounds incident to one
center is at most \(1/8\), for sufficiently large absolute \(C_0\).
The center-coincidence term is also bounded, since \(n\le\sqrt{nQ}\).
Each event has at most four center variables. The same product-form
local lemma as in the original construction therefore applies.

With these centers, every forbidden positive support has zero, one,
or at least two assigned labels. The profile hypotheses handle the
first two cases. The positional events handle the third. Thus this
is a complete identifying block with no empty columns and with
exactly the assigned doubles.

## 5. Sum the class widths

Let \(n_j,w_j\) be the nonempty dyadic classes. First,
\[
 \sum_j\sqrt{n_j}
 \le C\sqrt{Q(1+\log\Lambda)}.
 \tag{9}
\]
For \(w_j\le\Lambda^2\), there are only \(O(1+\log\Lambda)\)
classes, so Cauchy--Schwarz gives this bound. For larger \(w_j\),
(4) gives \(n_j\le C Q\Lambda/w_j\); the resulting geometric tail
is \(O(\sqrt Q)\).

Second, for every \(\eta>0\),
\[
 \sum_j w_j\sqrt{n_j}
 \le C_\eta\sqrt Q\,\Lambda^{3/2+\eta}.
 \tag{10}
\]
Apply (3) at \(2-d\) and \(2+d\), with fixed small \(d>0\),
and sum the two geometric tails around their balancing class.
The logarithmic exponent is
\[
 \frac{(2^{2-d}-1)+(2^{2+d}-1)}4
 =2\cosh(d\log2)-\tfrac12,
\]
which tends to \(3/2\) as \(d\downarrow0\).

Summing (8), using (9)--(10), gives
\[
 \sum_jN_j
 \le C_\eta Q
 \left(\Lambda^4\ell^C\sqrt{1+\log\Lambda}
       +\Lambda^{3+\eta}\right)
 \le C_\varepsilon Q\Lambda^{4+\varepsilon}.
 \tag{11}
\]
There are \(O(\log h)\) classes, so their bridges and collars cost
only \(O(h^2\log h)\). The profile family is bounded, and the
exceptional-label blocks cost \(O(h^2)\) by Section 1.
Constant tails then give every larger width. This proves the
theorem.

An absolute quadratic bound would still require a stronger placement
argument. The repeated-difference second moment in (6), not private
sea prescriptions, is the leading logarithmic cost in this proof.
