# Independent audit of protected-phase pressure

9 November 2026. This review covers `crossed_codegree_and_avoidance.md` and
`six_support_leading_pressure.md`. The first-order expansion in the exact
minimal-support mean and the three leading six-support constants pass the audit.
The mixed four-support coefficient and the unrestricted component comparison
remain separate questions.

## Overlap bounds and the probability input

The crossed-pair calculation is valid with the two fixed black cells in distinct
columns. Writing `n = pt+qs` and `K=s-2p`, the zero-determinant cases make one of
the two rectangles degenerate. Otherwise the displayed rational formulas for
the other black point are correct. The vertical strip bounds imply

\[
\min\{|s|,|s-2p|\}\le5(h-1).
\]

For `s != 0,2p`, the necessary divisibility

\[
n\mid K s^2(p^2+q^2)
\]

has a nonzero right side of polynomial size in `h`. Each signed divisor fixes
the remaining coordinates. The two exceptional values of `s` have only `O(h)`
possible vertical parameters. This proves the uniform `h^(1+o(1))` crossed-pair
bound.

The extension table for four- and six-cell supports is also valid. Two details
are useful when reading its six-cell cases. If three prescribed cells form one
whole black triple, they fix the common corner; the other rectangle then has
`O(h^2 log^2 h)` choices. If four prescribed cells split two and two, the common
corner lies in intersections of perpendicular lines or Thales circles. Any
coincident line is nonhorizontal because its defining black pair lies in
distinct columns, so it has only `O(h)` strip lattice points. Each remaining
completion is then determined.

Compatible events sharing `r` columns share exactly `r` prescribed cells.
The product of the first-event count, the extension count, and the joint
probability has exponent

\[
(s-1)+(t-r-1)-(s+t-r)=-2.
\]

Deduplication and inclusion minimality remove identical and containment pairs.
Conflicting assignments have joint probability zero. Thus the claimed
`Delta_m = O_epsilon(m h^(-2+epsilon))` follows.

I checked the primary author's text of
[Janson, *New versions of Suen's correlation inequality*](https://www2.math.uu.se/~svantejs/papers/sj121.pdf).
Section 2 uses independence of two entire indicator families whenever there is
no dependency edge between them, and defines `Delta` over unordered pairs.
Theorem 2 applies to arbitrary indicators with this strong dependency graph and
gives `P(S=0) <= exp(-mu + Delta exp(2 delta))`. The shared-column graph has
exactly the required independence property; no monotonicity assumption is being
imported.

The local-lemma lower bound with `x_E=(1+4 delta_m)p_E` is valid for sufficiently
small `delta_m`. Its logarithmic error is
`O(delta_m mu_m + sum p_E^2)`, of the asserted order. At fixed height, the bounded
support span makes finite-end conventions contribute only a bounded length
loss. This justifies the entropy limit

\[
\log r_X(h)=\bar\ell_X(h)-\mu_h+O_\varepsilon(h^{-2+\varepsilon}).
\]

## The leading six-support constants

For a fixed primitive direction `(a,b)`, the two extreme-corner roles contribute
`(H_+^2+H_-^2)/(2ab)` and the two intermediate roles contribute
`2H_+H_-/(ab)`. Summing the uniform floor errors gives `O(h^2 log h)`. Thus the
fixed-corner profile is

\[
D_h(r)=\frac{h^2\log^2h}{\zeta(2)}f(r/h)+O(h^2\log h),
\qquad f(t)=\tfrac12+t-t^2.
\]

As a consistency check, integrating `f` gives `2/3`, so summing this degree over
the rows gives four times the rectangle count.

The primitive parity types have equal leading harmonic weight. The conditional
scale factors are respectively `(1/4,1/2,1/2)` for O, `(1,1/4,1/4)` for C, and
`(1/2,1/4,1/4)` for Q. For Q with both primitive coordinates odd, exactly one of
the two odd-scale side conditions can hold at a fixed base parity; with opposite
primitive parities, each side allows two of its four scale residues. These give

\[
c_O=5/12,\qquad c_C=1/2,\qquad c_Q=1/3.
\]

The multiplicity exclusions are lower order. Reusing another black column costs
only `O(h^2)` choices for the second rectangle per fixed first rectangle and
common corner. A second description of the same six-cell support must introduce
a black right triangle mixing the two original triples. Its third point lies on
one of finitely many nonhorizontal perpendicular lines or Thales circles,
giving the same `O(h^2)` bound. A fixed four-support lies in only `O(h)`
six-supports: its cells split three and one or two and two, and the preceding
completion-locus argument applies. Repeated-column rectangles through the common
corner are likewise lower order. None changes the leading six-support count.

Finally, the unordered-pair factor and common-corner phase density give `1/4`;
the integral of `f^2` is `9/20`; and a six-cell event has probability
`(2/h)^6(1+O(1/h))`. Consequently

\[
\mu_{6,X}(h)\sim
\frac{36c_X^2}{5\zeta(2)^2}\frac{\log^4h}{h}.
\]

Substituting the three values of `c_X` gives, in order,
`45/pi^4`, `324/(5 pi^4)`, and `144/(5 pi^4)`. In particular the Q/O ratio is
`16/25` for this six-support contribution. This ratio alone does not order the
full phase entropies, because their minimal mixed four-support means must also
be evaluated.

## The mixed four-support order

The subsequent `mixed_four_logarithmic_lower_bound.md`, including its matching
upper bound, also passes this review. It proves the order
`Theta(log^4 h/h)` in each protected phase, without determining its coefficient.

For the lower bound, the primitive congruence count has the correct coefficient
`1/(3 zeta(2))` for odd coprime pairs. At a squarefree divisor `D`, the additional
local density is the product of `2/(p+1)`. Möbius inversion gives the displayed
error uniformly for `D <= h^(1/1000)`; its ratio to the main term tends to zero
uniformly over the prescribed dyadic boxes. Combining this density with the
divisibility weight from the side scale gives the Euler factor
`(4-2/(p+1))/p` at primes `p = 1 mod 4`.

The needed progression product follows from Theorem 1 of the primary paper
[Williams, *Mertens' Theorem for Arithmetic Progressions*](https://people.math.carleton.ca/~williams/papers/pdf/057.pdf),
which I checked directly. Restricting to primes at most `Y^(1/100)` and applying
Markov's inequality to the logarithm of their independently selected product
retains a fixed fraction of the Euler-product weight below `Y`. This supplies
two arithmetic logarithms; the disjoint dyadic direction boxes supply two more.

The geometric construction puts every required relative coordinate in `4Z`.
It consequently has a positive placement density in each of O, C, and Q. All
circle directions fit the strip by the chosen scale bounds. Only constantly
many representations per side/connector pair violate distinct columns or
nondegeneracy. The equal-length pairing of the four black cells, and its
side/diagonal roles, are unique unless `T dot V=0`, which forces the excluded
case `V=+U` or `V=-U`. A hidden rectangle likewise forces this degeneracy or
`T=0`. Thus the lower bound counts distinct minimal four-supports.

The upper bound uses elementary identities. If `rho(d)` counts roots of `-1`
modulo `d`, then `rho(d) <= r_2(d)/4`, so its summatory function is `O(X)` and
its harmonic sum is `O(log X)`. Prime-power comparison gives

\[
\frac{r_2(k^2)}4=\sum_{\substack{d\mid k\\d\text{ odd}}}\rho(d),
\qquad
r_2(k^2N)\le r_2(N)\frac{r_2(k^2)}4.
\]

For a primitive pair in an `A` by `B` dyadic box, each divisor of `a^2+b^2`
is coprime to `a`. The hyperbola estimate therefore gives the stated uniform
circle sum `O(AB log(2 max(A,B)))`. Summing with weights `1/(ab)` costs three
logarithms; the side-scale sum costs one more. Horizontal sides cost only two
logarithms, using `tau(v^2) <= d_3(v)`.

These bounds justify

\[
r_X(h)=h/2-\Theta(\log^4h)
\]

for each protected phase. Capture then gives the lower bounds
`h/2-O(log^4 h)` for both full boundary components under discussion. It does
not give a matching deficit bound for those full components. The mixed-family
coefficients, and hence the protected-phase ordering itself, are still open.

## Separated defects

`dilute_parity_defects.md` also passes the geometry and probability audit. Two
prescribed black points, together with a distinct prescribed completion column,
admit only constantly many rectangle completions: the possible completion is
on a perpendicular line or Thales circle, and a vertical line can coincide only
with one of the black columns, which is excluded.

Rooted singleton-event families have bounded incident probability and joint
overlap `O(log^2 h)` per defect. The rooted/bulk overlap estimate includes the
case in which a whole three-event is contained in a four- or six-event.
Independent constant thinning makes the rooted overlap quadratic in the
thinning parameter, while its mean is linear. Suen's bound therefore retains
the bulk mean and charges `exp(-c log^2 h)` per separated defect. Summing those
weights proves the stated dilute-class estimate. The checkerboard/Q extension
absorbs any one-row increase in a flipped column's alphabet into this penalty.
No claim about interacting defect clusters follows from this argument.

The later `clustered_parity_defects.md` supplies two further audited statements.
First, divisor pairing proves the uniform rearrangement bound
`sum_(d in D) tau(d)/d = O(log^2(|D|+1))` for arbitrary distinct distances.
The side-completion count has vertical step `d/gcd(d,v)`; the diagonal count is
subpolynomial. These give the stated rooted incidence, mean loss, and overlap
bounds. Cluster-dependent thinning then controls every cluster of size at most
`exp(a sqrt(log h))`. Its gap enumeration is dominated by the resulting penalty
when `a` is a sufficiently small absolute constant.

Second, Section 6 replaces the size bound by the weighted local-density condition
`D_h(S) <= kappa log h`. The additional local count term with coefficient
`h^(-7/8)` correctly bounds the number of possible completion columns in the
two-shared-cell case. Normalizing the thinning by each cluster's local density
keeps the global neighbor sum bounded. Small clusters use the distance
rearrangement bound; larger clusters have enough linear-in-size penalty to pay
for every gap choice. Only the at most `2L` end roots need be omitted, so an
unbounded cluster creates no unbounded end correction at fixed height.
This extension covers the stated infinite, sufficiently spread clusters. It
does not treat profiles with larger weighted local defect density.
# Polynomially spaced defects: additional review

The stronger exact comparison in `relative_sparse_defect_pressure.md` passes
review as well. Conditioning a rooted assignment leaves its entire
nonneighbor family in the original product distribution. The arbitrary-event
conditional local-lemma bound then controls each neighboring residual event.
Deduplicated rooted events share at most two assignments, and their total
conditional neighbor probability is `O(theta)+o(1)`. Every rooted event thus
retains at least half its original probability after any previously avoided
events. Sequential avoidance, conditional on the retained bulk, gives the
root penalty directly. Restoring omitted bulk costs only a factor depending
on the number of defects, so no extensive Suen error remains.

The defect-frequency corollary follows from binomial profile counting. For
frequency at least `delta=h^(-A)`, the entropy-per-defect term is at most
`A log h+O(1)`, whereas the penalty is of order `log^2 h`. The weighted-density
extension also passes: separate clusters have disjoint rooted variable sets,
and thinning by `b/D_C` controls both conditional overlap sums. The loss from
omitting boundary roots is `O_h(1)`, even for unbounded clusters. The note
consistently compares normalized support languages; it does not equate that
finite partition function with the rectangle-contained finite-prefix count.

The final explicit-divisor refinement also passes. Taking the maximum divisor
count `T_h` through the stated polynomial norm bound gives the same incidence
kernel with `T_h` in place of `h^eta`. Minimum spacing
`ceil(T_h (1+log h)^2)` makes the far-root contribution `O(1/log h)` and the
nearest diagonal contribution `O(T_h/h)=o(1)`. The elementary prime-factor
split proves `T_h=exp(O(log h/log log h))`. Thus a single subpolynomial spacing
condition suffices; the thinning and defect-penalty constants can be absolute.

The refined estimates in `polynomially_spaced_parity_defects.md` also pass
independent review. For a fixed diagonal endpoint pair with horizontal
separation `d`, orient the alternate diagonal with positive horizontal
component `z`. Writing `e=z-d`, the case `e=0` is degenerate or axis-aligned.
Otherwise `(v-w)(v+w)=e(2d+e)` has a nonzero right side of size `O(h^2)`.
There are `O(h^2/d)` possible nonzero values of `e`, and each gives
`h^{o(1)}` divisor pairs. Combining this with the direct circle bound gives
the claimed minimum of `h` and `h^2/d`.

For a side pair the vertical difference is nonzero, so summing the gcd count
does not introduce the earlier extra constant term. For two prescribed black
points in distinct columns, all possible completion points lie on constantly
many circles or nonhorizontal perpendicular lines. They contain `O(h)` strip
lattice points in total, independent of the number of defect columns. This
controls the two-assignment overlap without a separate local root-count term.

For roots separated by `h^alpha`, the two nearest roots contribute a bounded
amount to incidence at an arbitrary free column. The remaining roots contribute
`O(h^{eta-alpha} log h)` for any fixed `0<eta<alpha/2`. At a root itself every
other root belongs to this latter sum. Constant thinning therefore preserves
the rooted penalty of order `log^2 h` per defect, with only `o(1)` loss in its
mean. The existing retained-bulk and profile-sum arguments apply without a
bound on cluster size. This result still does not control profiles with
arbitrarily small spacing relative to every fixed power of the height.

