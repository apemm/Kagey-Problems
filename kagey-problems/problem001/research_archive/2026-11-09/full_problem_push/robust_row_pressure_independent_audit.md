# Independent audit of robust row-perturbation pressure

9 November 2026. The theorem in robust_row_perturbation_pressure.md
passes independent review under its stated protected-reference
hypotheses. It gives exact fixed-phase pressure
\(\exp(-c rm/h)\) throughout \(1\le r\le\delta_0h\),
and the stated strict comparison after summing arbitrarily clustered
phase errors of sufficiently small total density.

For a changed completion row \(w\), the vectors
\[
 U=(4,4\epsilon u),\qquad V=(-4uv,4\epsilon v)
\]
are perpendicular. Their vertical span is at most \(4h/25\).
Choosing the sign toward the farther boundary puts every corner
inside the strip. All coordinate changes are multiples of four,
so every protected row/column law is preserved. The three black
corners are distinct and determine their completion.

There are \(\Theta(h^2)\) choices of \((u,v)\). Excluding any
changed black row removes at most \(O(h)\) choices, because it
fixes \(u\), \(v\), or \(u+v\). Thus \(r\le\delta_0h\), with
small absolute \(\delta_0\), leaves a fixed fraction.

The overlap bounds have no hidden divisor loss. A fixed black cell
and root row fix one parameter or their sum, leaving \(O(h)\)
choices. For two fixed black cells:

* the \(U\)-separated pair fixes \(u\), and the root row fixes \(v\);
* the \(V\)-separated pair fixes \(v\) and then \(u\);
* the remaining pair fixes \(uv\) and \(v-u\), giving at most two
  positive parameter pairs.

There are only finitely many point roles and signs. Hence the
one-cell and two-cell counts are \(O(rh)\) and \(O(r)\).
Both raw incident pressure and compatible conditional pressure
are \(O(r/h)\), uniformly in the changed row set. A sufficiently
small absolute \(\delta_0\) makes the unthinned local lemma and
the exact conditional event bound applicable.

Retaining only old bulk certificates whose entire geometry avoids
the changed rows preserves their joint law under the alphabet
correspondence. Restoring the deleted certificates costs
\(O_\varepsilon(rm h^{-2+\varepsilon})\), which is uniformly
smaller than \(rm/h\) for any fixed \(\varepsilon<1\).
The bounded alphabet-size mismatch costs \(O(m/h)\): large \(r\)
absorbs it, while bounded \(r\) is handled by the previously
audited stronger logarithmic penalties.

For arbitrary phase-error columns \(S\), deleting roots whose black
or completion columns meet \(S\) loses \(O(|S|r/h)\) mean.
All retained events avoid those columns, so arbitrary clustering
does not affect the product-space comparison. Restoring old bulk
there costs \(O(|S|\log^4h/h)\).

Finally, with \(q=r/h\) and
\(\sigma\le bq/\log(e/q)\), the entropy of error locations obeys
\[
 H_2(\sigma)\le Cb(1+\log(1/b))q.
\]
Choosing \(b\) sufficiently small makes this smaller than the row
pressure. The other restoration term divided by \(q\) is at most
\(Cb\log^4h/[h\log(e/q)]\), uniformly tending to zero.
This verifies the strict comparison in the stated density range.

The result requires closeness to one global protected phase.
Several domains occupying positive fractions of the word are not
included.

Section 5's explicit extension to the slightly unbalanced reference
also passes. The protected law \(q(y)+y\) has class sizes
\(h/2\pm1\) at heights \(h\equiv2\pmod4\), while the new
balanced coloring has sizes \(h/2\). Each alphabet therefore
changes by at most one letter. Every matched quadratic phase is
nonconstant, so each changed row remains eligible in half the
columns, including \(r=1\). There is no missing-root constant-phase
exception. The same dummy-letter argument handles large \(r\),
and the full logarithmic completion-root family handles bounded
\(r\). The stated extension therefore covers every protected
reference supplied by asymptotic row rigidity.

## A shorter alternative rectangle family

The subsequent replacement
\[
 U=(4u,4\epsilon u),\qquad V=(-4v,4\epsilon v)
\]
also passes review and preserves the theorem. It has the same
number of parameter choices, changed-row exclusions, and
\(O(rh)\), \(O(r)\) conditional overlap counts. For the pair
\(P,Q\), its horizontal difference fixes \(u+v\), and its
vertical difference fixes \(v-u\). The other two pair roles
fix one side and then the second parameter from the root row.

When \(u=v\), the missing corner and \(R\) share a column.
The three required black columns remain distinct. Since the
missing row changes class while \(R\)'s row does not, the same
singleton rival still occurs. This case does not create a repeated
required variable or invalidate the count.

The horizontal span is now \(4(u+v)=O(h)\), so the lost
finite-end mean is \(O(r)\). This strengthens the endpoint
constant without changing the extensive penalty.
