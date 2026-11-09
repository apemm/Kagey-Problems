# An exact finite-width encoding with row-pair owners

The compact axis-rival model extends from a fixed row-pair set to arbitrary boards. It does not require an equality construction, a prescribed row partition, or singleton/double columns.

Assume \(h,m\ge4\). Let \(b_{r,j}\) mean that the point in row \(r\), column \(j\) is black. For every unordered row pair \(a<b\), introduce

\[
E_{ab,j}\ \longleftrightarrow\ b_{a,j}\land b_{b,j},
\qquad
F_{ab}\ \longleftrightarrow\ \bigvee_j E_{ab,j}.
\tag{1}
\]

The variable \(E_{ab,j}\) records a column containing both rows. When the axis constraints hold, that column is unique whenever it exists.

## A compact exact encoding of the axis condition

First impose at most one \(E_{ab,j}\) over all columns \(j\), separately for every row pair. This is exactly the absence of an incidence 4-cycle.

For every row triple \(a<b<c\) and every column \(j\), impose

\[
E_{ab,j}\land F_{ac}\land F_{bc}
\quad\Longrightarrow\quad E_{ac,j}.
\tag{2}
\]

Together with the pair-uniqueness constraints, (2) is exactly the absence of an incidence 6-cycle.

To see this, suppose all three row pairs \(ab,ac,bc\) occur. Let \(j\) own \(ab\). Equation (2) puts \(ac\) in column \(j\), so all three rows are black in that column. Equation (1) then puts \(bc\) there as well. All three row pairs have the same owner.

Conversely, in a family with no incidence 4-cycle or 6-cycle, three occurring row pairs cannot have three distinct owners. If any two have the same owner, their column contains all three rows, so the third owner must also coincide by pair uniqueness. Therefore all three owners coincide, and (2) holds.

The incidence characterization of axis identification is exactly the absence of 4-cycles and 6-cycles. Thus (1), pair uniqueness, and (2) encode the full axis requirement. With pairwise at-most-one constraints, their size is

\[
O(h^2m^2+h^3m)
\]

clauses and \(\binom h2(m+1)\) additional variables. The explicit 6-cycle list would instead have order \(h^3m^3\) clauses.

## Tilted-axis collisions without axis witnesses

For every tilted rectangle \(R\), forbid all four of its corners from being black. This is necessary by `hidden_rectangles_and_exact_hypergraph.md`.

For each corner \(P=(j,r)\in R\) and each row \(s\ne r\), forbid the conjunction

\[
F_{rs}\land b_{s,j}\land
\bigwedge_{Q\in R\setminus\{P\}} b_Q.
\tag{3}
\]

If \(P\) is white, the row-pair occurrence supplied by \(F_{rs}\) lies in another column and creates an axis rectangle with the same singleton presentation. If \(P\) is black, \(R\) is hidden. Therefore the conjunction is forbidden without a white literal for \(P\).

For two corners \(P=(j,r)\), \(Q=(j,s)\) in one column, forbid

\[
F_{rs}\land
\bigwedge_{T\in R\setminus\{P,Q\}} b_T.
\tag{4}
\]

If at least one of \(P,Q\) is white, the row pair occurs in another column and gives an axis rival. If both are black, \(R\) is hidden.

For a horizontal prospective white pair \(P=(i,r)\), \(Q=(j,r)\), use the four-point supports

\[
(R\setminus\{P,Q\})\cup\{(i,s),(j,s)\},
\qquad s\in[h].
\tag{5}
\]

For an oblique prospective white pair \(P=(i,r)\), \(Q=(j,s)\), use

\[
(R\setminus\{P,Q\})\cup\{(i,s),(j,r)\}.
\tag{6}
\]

The proofs of (5) and (6) are the same direct axis-rival arguments as in `compact_equality_sat.md`. They remain valid when some prospective white corners are black.

## Completing the exact model

For each pair of tilted rectangles sharing a corner, forbid their symmetric difference from being black. These supports have four or six points. No disjoint pair has to be listed, since such a collision would require hidden rectangles.

The resulting model is exact:

* The owner constraints handle every axis-axis collision.
* Equations (3) through (6) handle every tilted-axis collision.
* The tilted symmetric differences handle the remaining nonempty presentations.
* The no-hidden constraints handle empty presentations.

One can then impose any desired black-point count, or maximize that count. This is a finite-width mechanism for the general function \(f(h,m)\), with no fixed partition or column multiset.

Any extra structural restriction must still be proved separately. The seven-row implementation adds the large-column bound when its target count implies it. At excess ten, it also uses the proved uniqueness of a triple column. Neither restriction is assumed at lower excess.

## Implementation and checks

The `owners` option in `seven_row_general_sat.py` implements this model at height seven. At width 12 and target 22, it has 1,457 variables and 56,686 clauses, compared with 204,080 clauses in the direct four/six-support model.

`audit_pair_owner_sat.py` compares the model with direct full-rectangle identification on 612 fixed boards at widths 11, 12, and 13. The cases include the known valid constructions and their reflections, together with random point swaps preserving the black count. The two independent rectangle generators agree in all three dimensions. Every SAT decision under the fixed point assignments matches the direct presentation check. The audit includes valid boards with two triple columns, so it checks that genuine one-column row triangles are permitted.

The initial unrestricted width-12/22-point owner-model run reached its 180-second cap without deciding the instance. This is `unknown`, not an upper-bound certificate. The independently completed structural ordering search proves \(f(7,12)=21\).

The smaller encoding is an exact modeling improvement. It does not itself settle the square exponent or the seven-row equality threshold.
