# Independent audit of the sharper logarithmic threshold

9 November 2026. The theorem in sharper_polylogarithmic_threshold.md
passes independent review. The resulting bound is
\[
m_0(h)\ll_\varepsilon h^2(1+\log h)^{8+\varepsilon}.
\]
The review covers the external moment input, the geometric weight
reduction, the event estimate, and the summation over arithmetic classes.

## 1. The primary theorem and erratum

Henriot's upper bound applies to primitive polynomial products, with
uniform constants once the degree, arithmetic-function growth parameters,
and size exponents are fixed. The interval translation gives
\(x=y=h\), and the polynomial height is \(O(h^2)\), so \(\delta=1/3\)
satisfies the size requirement for large \(h\). A fixed choice such as
\(\alpha=1/2\) satisfies the interval requirement. Contents of linear forms
with bounded nonzero leading coefficients are bounded.

The erratum retains the upper bounds and replaces the exceptional-prime
parameter by \(a^*D^*\), including the squarefree polynomial's leading
coefficient. Its congruence-function correction only decreases the old
upper majorant. Sources: [original Corollary 2](https://arxiv.org/html/1102.1643)
and the [2014 erratum](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B0BD208D979495FE06B8192209E710EA/S0305004114000280a.pdf/nairtenenbaum_uniform_with_respect_to_the_discriminanterratum.pdf).

For \(\tau(L_1L_2)^s\), distinct primitive linear factors give ordinary-prime
coefficient \(2(2^s-1)\). A repeated factor gives \(3^s-1\).
The latter dominates for \(s\) in a fixed neighborhood of two.
Exceptional primes contribute at most a fixed power of
\(1+\log\log(3h)\). The contents, leading coefficients, and resultants
have the uniform bounds stated in the proof.

The moment assertion requires both affine factors to be nonconstant
in the variables being averaged. A constant factor depending on \(h\)
would not have a uniform polylogarithmic divisor bound. The geometry
argument correctly isolates those factors rather than applying the
moment theorem to them.

## 2. Why the height-only list is complete

A genuine support uses each black cell only once. If two occurrences
were the same endpoint of one label, they would be the same cell,
which is forbidden in the four-distinct-corner support classification.
Consequently a label variable cannot disappear from a mixed row sum
through a repeated symbolic occurrence of that endpoint. Numerical
coincidences between rows of different labels are filters that can be
discarded when taking an upper bound over the full row box.

For a mixed support with nonvertical side, the divisor product is
\[
yH_y=(b'-a')(a'+b'-c'-d').
\]
The side difference can be independent of every label variable only
when both side points are actual sea points. The side then joins rows
\(1,g\). Its nonzero perpendicular translation raises both endpoints
by an integer \(j\) satisfying
\[
1\le j\le h-g\le3,\qquad x\mid j(g-1).
\]
The zero translate is degenerate.

For a private one-label support, the other diagonal cannot consist
of both central points: its vertical length is at most \(g-1\), shorter
than the oblique side. If it uses a central point and a sea point,
the sea point must be at row \(g\), forcing central row \(1+2j\le7\).
This is exactly the exceptional term in the row weight.

For a support with at least two labels, that same side uses no labels,
so its two diagonal points must use exactly two different labels.
Their row sum is \(1+g+2j\). Fixing one label fixes the other selected
row, leaving only \(O(h)\) choices for its mate. Thus the total squared
contribution is \(O(h\tau(g-1)^2)=O(h^2)\).

In the horizontal-side case, the divisor product is the square of
the black diagonal's row difference. A diagonal joining sea rows
\(1,g\) has half-integral midpoint because \(g\) is even. Repeating a
sea row gives a degenerate horizontal alternative. Neither creates
another height-only family.

A three-black support using at least two labels has at most one sea
point, so neither vertical-leg factor can be the difference of the
two sea rows. In the private case, adjacent sea points force the
central row at most \(h-g+1\le4\), giving the stated low-row exception.
Vertical parity rivals involving two labels have a varying row
difference; equal-row diagonals are parity-safe.

This accounts for every fixed height-only factor in the private and
multi-label counts. A factor fixed after conditioning on an edge but
still depending on that edge belongs to the row-weight family.

## 3. Moment and event estimates

Retaining \(\tau(L_1L_2)\) directly gives row weights with moments
\[
\sum_e w(e)^s\ll_s Q\Lambda^{3^s-1}\ell^{C_s}
\]
near \(s=2\). The \(O(h)\) exceptional labels are harmless even above
moment two: the elementary subpower bound gives
\(\tau(g-1)^s\ll_s h^{1/2}\).

For a fixed label, if both row factors vary, the product moment applies.
If exactly one is fixed, submultiplicativity extracts
\(\tau(c(e))^2\le Cw(e)^2\), and the varying factor's second moment
has exponent three. If both are fixed, their product is covered by
the row weight. The exceptional family in Section 2 has the separate
\(O(Q)\) bound. This proves the squared geometry estimate with
\(\Lambda^8\ell^C\).

The local-lemma calculation is unchanged after its square root:
the class length \(nw^2+\sqrt{nQ}\,w\Lambda^4\ell^C\) controls overlaps
and every geometric arity. All supports still use at most four center
variables. The original sea completion and global pair-set tests
therefore retain their scope.

Also \(w(e)=O(h)\), since each nonzero product has size \(O(h^2)\) and
\(\tau(n)\le2\sqrt n\). Thus the number of nonempty dyadic classes,
and hence the number of collars, remains \(O(\log h)\).

## 4. The two-moment summation

For \(A_\pm=\sum_j n_jw_j^{2\pm d}\), split the dyadic sum at \(W\).
The individual class bounds give
\[
\sum_jw_j\sqrt{n_j}
\ll_d \sqrt{A_-}W^{d/2}+\sqrt{A_+}W^{-d/2}
\ll_d(A_-A_+)^{1/4}.
\]
This is a sum of two geometric series, so no factor counting the
classes is introduced. Substituting the two moment bounds yields
the exponent
\[
4+\frac{\beta(2-d)+\beta(2+d)}4
=8+\frac92\bigl(\cosh(d\log3)-1\bigr).
\]
Choose fixed \(d>0\) sufficiently small, then absorb the remaining
fixed power of \(\ell\) into \(\Lambda^\varepsilon\).
The collar cost is smaller. No additional independence or geometric
assumption is required by this refinement.

