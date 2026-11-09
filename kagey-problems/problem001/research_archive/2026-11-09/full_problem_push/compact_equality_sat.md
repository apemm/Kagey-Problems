# Eliminating axis witnesses from equality SAT instances

Fix a row partition \(A\sqcup B=[h]\). Consider column families with exactly one double column for every pair in \(A\times B\), and singleton columns everywhere else. Write \(F=A\times B\) for this complete row-pair set. The axis presentations are already distinct.

The exact geometric constraints can be compiled without enumerating all axis rectangles. This eliminates long families of six-point clauses whose axis witness is guaranteed by \(F\).

Assume \(h,m\ge4\), so the no-hidden-rectangle theorem applies.

## The positive forbidden supports

For each tilted rectangle \(R\), include its four corners as a forbidden black support. Also include the following supports. A support is discarded when the fixed column structure makes it impossible.

**One prospective white corner.** Let \(P=(c,r)\in R\). For every row \(s\) in the opposite partition class from \(r\), forbid

\[
(R\setminus\{P\})\cup\{(c,s)\}.
\tag{1}
\]

This support has at most four points and can have three when the added point is already a corner of \(R\).

**Two prospective white corners in one column.** Let \(P=(c,r)\), \(Q=(c,s)\) be corners of \(R\). If \(r,s\) lie in opposite partition classes, forbid

\[
R\setminus\{P,Q\}.
\tag{2}
\]

This is a two-point constraint.

**Two prospective white corners in one row.** Let \(P=(c,r)\), \(Q=(d,r)\). For every row \(s\), forbid

\[
(R\setminus\{P,Q\})\cup\{(c,s),(d,s)\}.
\tag{3}
\]

**An oblique prospective white pair.** Let \(P=(c,r)\), \(Q=(d,s)\), with \(c\ne d\) and \(r\ne s\). Forbid

\[
(R\setminus\{P,Q\})\cup\{(c,s),(d,r)\}.
\tag{4}
\]

Finally, for every pair of distinct tilted rectangles sharing a corner, forbid their symmetric difference. These supports have four or six points.

## Why the constraints are exact

The phrase "prospective white" specifies the role of a corner, not an additional white literal in a clause. The positive supports remain forbidden even when one of those corners happens to be black.

For (1), if \(P\) is white, the black point \((c,s)\) and the guaranteed double column for \(\{r,s\}\in F\) give an axis rectangle whose only white corner is \(P\). Its presentation equals that of \(R\). The double column is distinct from \(c\), since \(P\) is white. If \(P\) is black, \(R\) is hidden and invalid.

For (2), the guaranteed double column for \(\{r,s\}\in F\) supplies an axis rectangle sharing \(P,Q\). If at least one of \(P,Q\) is white, that double column is distinct from \(c\), and the two presentations agree. If both are black, \(R\) is hidden.

For (3), the two added points complete the axis rectangle sharing \(P,Q\). The two rectangles have identical presentations regardless of which of \(P,Q\) are white. When \(s=r\), the support is simply all of \(R\), so the no-hidden condition applies instead of a degenerate axis rectangle.

For (4), the two added crossed points are the other corners of a nondegenerate axis rectangle. It is distinct from the tilted \(R\), and their presentations agree whenever the listed support is black.

Conversely, any axis rival of a tilted presentation has zero, one, or two white corners. Zero is covered by the hidden support. The exact axis-rival criterion for one or two white corners gives respectively (1), (2), (3), or (4). A presentation with at least three white corners determines its rectangle uniquely. Tilted-tilted collisions are covered by the listed symmetric differences; disjoint tilted rectangles could collide only if both were hidden.

Therefore these constraints, together with the fixed column structure, are equivalent to full rectangle identification.

## Feasibility and inclusion reductions

A positive support cannot be black when it requires any of the following:

* Three points in a single column.
* Two rows in a column that do not form an edge of \(F\).
* The same double row pair in two different columns.

Such supports are omitted. Of the remaining supports, any support containing a smaller forbidden support is redundant and is omitted as well. Both reductions preserve exactness.

This argument applies to every complete bipartite row partition, including nonparity partitions. The special two-point constraints in (2) recover the Pythagorean pair obstructions in a form that a SAT solver can propagate immediately.

## Seven-row implementation and calibration

The `compact` option in `seven_row_equality_sat.py` implements this formulation. For the parity partition at width 20, it has 520 variables and 61,511 clauses. The earlier exact four/six-support implementation had the same variables and 292,267 clauses. The older stored encoder had 2,795 variables and 338,176 clauses.

The inclusion-minimal geometric supports in the compact width-20 instance are:

| Support size | Count |
|---:|---:|
| 2 | 64 |
| 3 | 0 |
| 4 | 21,370 |
| 6 | 33,584 |

There are 128 three-point supports before inclusion reduction; all contain a forbidden two-point support.

`audit_equality_encoder.py compact` checks every compiled clause against the stored valid width-21 construction. It passes all 66,455 clauses of that instance. Any SAT witness returned by the solver is also checked against the complete rectangle list.

The formulation is an exact model, not a proof that width 20 is feasible or infeasible. The compact width-20 parity pilot reached its 300-second cap with status `unknown`. The 18 remaining balanced partitions, up to vertical reflection, each reached a 10-second pilot cap with status `unknown`. These runs carry no upper-bound conclusion.
