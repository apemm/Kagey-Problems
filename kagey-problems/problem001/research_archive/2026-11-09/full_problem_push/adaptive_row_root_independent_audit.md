# Independent audit of adaptive row-root pressure

9 November 2026. adaptive_row_root_pressure.md passes independent
review in its stated range \(R_0\le r\le\delta_0h\). Its exact
fixed-phase penalty is
\[
 \exp\!\left[-c(r/h)\log^2(h/r)\,n\right],
\]
with rooted-family endpoint loss \(O(\sqrt{rh})\).

The primitive parametrization has bounded multiplicity: the positive
horizontal side and its primitive direction determine \(a,b,k\);
the other side determines its scale. The primitive harmonic sum is
\(\Theta(\log^2R)\). Since \(R\le\sqrt h\), every scale interval
has enough integers uniformly for large \(h\).

Each changed black row fixes one scale, or fixes the second scale
after the first is chosen. Summing these slices gives
\(O(rhR\log R)\) deletions per completion row. Compared with
the \(\Theta(h^2\log^2R)\) initial count, this has relative size
\(O((r/h)R/\log R)\). A sufficiently small absolute
\(\delta_0\) leaves a fixed fraction.

For one fixed black cell and completion row, the side roles have
at most \(R\) possible divisors and \(O(h\log R)\) remaining
choices. The opposite-corner role uses the coprime equation
\(kb+\ell a=d\), with
\(O(h/(ab)+1)\) solutions per direction.
This proves \(O(hR\log R)\), uniformly in the row and cell.

For two fixed black cells, their completion lies on a circle or
one of a bounded number of perpendicular lines. A perpendicular
line could be horizontal only if the fixed cells shared a column,
which genuine support cells do not. A prescribed completion row
therefore leaves only \(O(1)\) possibilities. The total conditional
counts are consequently \(O(rhR\log R)\) and \(O(r)\), with no
hidden maximum-divisor factor.

At \(R=\lfloor\sqrt{h/r}\rfloor\), raw and conditional pressure
are \(O(\sqrt{r/h}\log(h/r))\). Choosing \(\delta_0\) small
makes the unthinned local lemma and exact conditional event lower
bound valid. The three required black columns remain distinct
even when the missing corner shares the opposite corner's column.
That shared column does not change the singleton rival.

The first span moment over directions \(a,b\le R\) is
\(O(h^3R)\) per root row. Dividing by the three-letter event
denominator and summing the \(r\) root rows gives \(O(rR)\),
which is at most \(O(\sqrt{rh})\). Both the old-bulk restoration
and the one-letter alphabet-size mismatch are absorbed as stated.
The protected crossing-weight bound then supplies the final
\(\exp(O(h\log^2h))\) endpoint factor.

The lower cutoff \(R_0\) keeps the isolated growing-even-class
exception outside this theorem. That case remains covered by
the separate two-point vertical-rival argument, not by a
completion-root family with no eligible root.

The result is an exact fixed-phase comparison. It does not extend
to arbitrary phase profiles without their additional counting and
interface costs.
