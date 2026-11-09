# Independent audit of the fixed two-moment threshold

9 November 2026. The refinement in
two_moment_threshold_refinement.md passes independent review.
There are absolute constants \(C_0,C_1>0\) such that
\[
 m_0(h)\le C_0h^2(1+\log h)^2
                    (1+\log\log(3h))^{C_1}.
\]
The underlying safe-triangle geometry and complete finite-end
construction were reviewed separately in
safe_triangle_first_moment_independent_audit.md.

The weighted arithmetic proof is valid at class-weight exponent
two. Its functions remain submultiplicative with subpower growth.
For distinct roots, the relevant prime coefficients are five for
\(\tau(C)^2\tau(A^2)\) or
\(\tau(C)^2\tau(A)\tau(B)\), and four for
\(\tau(C)^2\tau(A)\). These are precisely
\(\beta(2)+2\) and \(\beta(2)+1\).
The finite exceptional slices are still estimated separately by
the uniform subpower bound. Since only exponents one and two are
used, all exceptional-prime powers of the second logarithm are
absolute constants.

With \(\Lambda=1+\log h\), the three bounds
\[
 M(w)\le1,\qquad M(w)\ll\Lambda/w,\qquad
 M(w)\ll\Lambda^3/w^2
\]
give \(\sum_wM(w)\ll1+\log\Lambda\).
For \(wM(w)\), the ranges below \(\Lambda\), between
\(\Lambda\) and \(\Lambda^2\), and above \(\Lambda^2\)
contribute respectively \(O(\Lambda)\),
\(O(\Lambda(1+\log\Lambda))\), and \(O(\Lambda)\).
The claimed pair budget follows.

The new higher-arity estimate is also correct:
\[
 \sum_w\sqrt{w n_w}
 \ll\sqrt Q\sum_w\sqrt{wM(w)}
 \ll\sqrt{Q\Lambda}\,(1+\log\Lambda).
\]
In the outer ranges these are geometric sums of \(\sqrt w\)
and \(\Lambda^{3/2}/\sqrt w\). In the middle range each
term is \(O(\sqrt\Lambda)\). Combined with
\(\sum_w\sqrt{n_w}\ll\sqrt{Q(1+\log\Lambda)}\), this
makes the second term in the higher-arity budget
\(O(Q\Lambda^{5/4}(1+\log\Lambda))\), as written.
No missing main-logarithm factor occurs.

The collar and exceptional-label costs are smaller. Constant tails
provide all larger widths, and increasing \(C_0\) covers the
finitely many heights below the explicit profile range.
The simultaneous counting consequence inherits the previously
audited construction/core gluing: one additional main logarithm
pays for the deterministic reserved columns. Its stated regime is
therefore consistent with the new threshold.
