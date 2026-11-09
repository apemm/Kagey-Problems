# An exact SAT encoding linear in the number of rectangles

9 November 2026. This result applies to arbitrary finite point configurations and arbitrary blackouts. It avoids enumerating all pairs of rectangles. It does not determine the extremal value by itself.

Let \(V\) be the available points, let \(N=|V|\), and let \(\mathcal R\) be the nondegenerate rectangles with vertices in \(V\). Write \(M=|\mathcal R|\). A blackout \(B\subseteq V\) is valid when the presentations \(R\setminus B\), for \(R\in\mathcal R\), are distinct.

**Theorem.** Validity has an existential CNF encoding with the \(N\) point variables, at most \(22M\) auxiliary variables, and at most \(44M\) clauses. The incidence lists needed for the encoding have total length \(O(M)\). For an integer grid with both dimensions at least four, the no-hidden theorem reduces the bounds to \(20M\) auxiliary variables and \(41M\) clauses.

The constants are loose. They make the linear size explicit.

## The three families of constraints

Let \(b_v\) indicate that \(v\) is black. Every auxiliary flag below has a one-way trigger. Equivalence clauses are unnecessary.

For every distinct pair \(Q=\{a,b\}\) contained in a rectangle, introduce \(x_Q\) and the clause
\[
\neg b_a\lor\neg b_b\lor x_Q.
\tag{1}
\]
For every pair \(P\) contained in a rectangle, impose at most one on the list
\[
\bigl(x_{R\setminus P}:R\in\mathcal R,\ P\subseteq R\bigr).
\tag{2}
\]
The entries within this list are distinct. Two equal complement pairs, together with the same \(P\), would give the same rectangle.

For every rectangle \(R\) and corner \(p\in R\), introduce \(a_{R,p}\), triggered by the other three corners:
\[
\left(\bigvee_{v\in R\setminus\{p\}}\neg b_v\right)\lor a_{R,p}.
\tag{3}
\]
For every point \(p\), impose at most one on
\[
\bigl(a_{R,p}:R\in\mathcal R,\ p\in R\bigr).
\tag{4}
\]

Finally, introduce \(z_R\) for each rectangle, with trigger
\[
\left(\bigvee_{v\in R}\neg b_v\right)\lor z_R,
\tag{5}
\]
and impose at most one on all \(z_R\). This permits one hidden rectangle, as the original definition requires.

## Exactness

Two distinct nondegenerate rectangles cannot share three vertices: three vertices of a rectangle contain a unique right-angle vertex and determine the fourth vertex. Thus their intersection has size zero, one, or two.

If two rectangles have the same presentation, every vertex outside their intersection is black. If they share two points \(P\), the two corresponding complement-pair flags in (2) are forced true. If they share one point \(p\), the two triple flags in (4) are forced true. If they are disjoint, both are hidden, so two flags in (5) are forced true. Every invalid blackout therefore violates a required at-most-one condition in every extension to the auxiliary variables.

Conversely, assign each flag its actual conjunction of black point variables. If two entries in (2) are true, both rectangles have presentation \(P\setminus B\). If two entries in (4) are true, both have presentation \(\{p\}\setminus B\). If two hidden flags are true, both presentations are empty. A valid blackout therefore extends to a satisfying assignment.

This argument also explains why no white-corner literals are needed. Changing a shared point from white to black changes both presentations in the same way.

## Linear size

An at-most-one condition on \(k\ge2\) variables \(u_1,\ldots,u_k\) uses \(k-1\) prefix flags \(s_1,\ldots,s_{k-1}\) and the clauses
\[
\begin{array}{ll}
\neg u_i\lor s_i,&1\le i<k,\\
\neg s_{i-1}\lor s_i,&2\le i<k,\\
\neg u_i\lor\neg s_{i-1},&2\le i\le k.
\end{array}
\]
These clauses force every later \(u_i\) false after an earlier true entry. Conversely, with at most one true entry, setting \(s_i=\bigvee_{j\le i}u_j\) satisfies them. The size is \(k-1\) variables and \(3k-4\) clauses. Lists of length zero or one need no clauses.

There are at most \(6M\) distinct pair flags, exactly \(4M\) triple flags, and \(M\) hidden flags. The total lengths of the lists (2), (4), and (5) are \(6M\), \(4M\), and \(M\). Hence the at-most-one encodings use at most \(11M\) further variables and \(33M\) clauses. The trigger clauses contribute at most \(11M\), giving the stated \(22M\) and \(44M\) bounds.

On a grid with both dimensions at least four, every hidden rectangle is forbidden by the no-hidden theorem. Replace the \(M\) hidden flags and their global at-most-one condition by the \(M\) clauses \(\bigvee_{v\in R}\neg b_v\). The remaining flags and prefix variables total at most \(20M\), and the clauses total at most \(41M\).

## Consequence for exact finite-width optimization

An exact black-count constraint can use \(O(N^2)\) further variables and clauses. For example, let \(t_{i,j}\) mean that at least \(j\) of the first \(i\) points are black, and encode
\[
t_{i,j}\longleftrightarrow
t_{i-1,j}\lor(t_{i-1,j-1}\land b_i)
\]
with the usual boundary constants. Requiring \(t_{N,k}\) and \(\neg t_{N,k+1}\) imposes exactly \(k\) black points. Each recurrence needs only a bounded number of clauses.

On an \(h\times m\) grid with \(h,m\ge2\),
\[
M\ge\binom h2\binom m2\ge\frac{(hm)^2}{16}=\frac{N^2}{16}.
\]
Thus the entire exact decision problem, including the target cardinality, has CNF size \(O(M)\). This gives an exact alternative to generating \(O(M^2)\) rectangle-pair differences. It makes no claim about the time required to solve the resulting CNF.

The companion standard-library checker compares these three conjunction tests with direct presentation injectivity on every blackout of the \(2\times2\), \(3\times3\), \(3\times4\), and \(4\times4\) grids. The small-grid cases retain the global hidden condition and include valid blackouts with one hidden rectangle.

## Exact counting without projection

The one-way triggers give an existential encoding. A valid blackout can have several auxiliary extensions, so ordinary model counting of that encoding would overcount. A linear-size modification removes this ambiguity.

For every flag \(z\) representing a conjunction of \(d\) black point variables, add the \(d\) reverse clauses \(\neg z\lor b_v\). Together with the trigger, this forces the exact conjunction and uses \(d+1\) clauses. The pair, triple, and hidden flags therefore need three, four, and five clauses each.

For each at-most-one list \(u_1,\ldots,u_k\), force the prefix flags to have their exact meanings. Use
\[
s_1\longleftrightarrow u_1,
\qquad
s_i\longleftrightarrow(s_{i-1}\lor u_i)
\quad(2\le i<k),
\]
and retain \(\neg u_i\lor\neg s_{i-1}\) for \(2\le i\le k\). The first equivalence needs two clauses, each later equivalence needs three, and the exclusion clauses contribute \(k-1\). For \(k\ge2\), the total is \(4k-5\) clauses and \(k-1\) auxiliary variables.

Every point assignment now determines every conjunction flag and every prefix flag uniquely. It has one satisfying auxiliary extension exactly when the blackout is valid. Consequently ordinary model counting, without projection, counts valid blackouts exactly.

The general encoding still uses at most \(22M\) auxiliary variables. The conjunction equivalences require at most
\[
3(6M)+4(4M)+5M=39M
\]
clauses, and the three families of prefix constraints require at most \(4(11M)=44M\). Thus **\(83M\) clauses suffice for a parsimonious encoding**. On grids with both dimensions at least four, omit the hidden flags and add the \(M\) no-hidden clauses. The corresponding bounds are **\(20M\) auxiliary variables and \(75M\) clauses**.

The exact cardinality recurrences in the preceding section also determine their auxiliary variables uniquely. Adding them preserves the one-to-one correspondence. In particular, ordinary model counting with target \(k=f(h,m)\) gives the number of maximum blackouts, provided that target value has been established separately.

`presentation_fiber_cnf.py` implements both versions. Its companion `verify_presentation_fiber_cnf.py` enumerates all complete SAT models of the parsimonious encoding on the four small grids. The counts are 16, 292, 1,510, and 8,757. Each count agrees with direct presentation checking, and no blackout has two auxiliary extensions. The recorded result is `presentation_fiber_cnf_check.json`.
