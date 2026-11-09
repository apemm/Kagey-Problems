# A local pressure cost at a protected-phase domain wall

9 November 2026. A change between two protected column laws creates a family of singleton rivals within distance \(O(h)\) of the change. The resulting count comparison uses the exact partition function of each individual domain. It does not yet compare the full count with a single Perron exponential.

Fix a balanced protected row law
\[
 c_0(y)=\kappa q(y)+\alpha y+\beta,
\]
where \(\alpha=1\) if \(\kappa=0\), and let
\[
 \mathcal X=\{\kappa q(x)+\gamma x+\delta:\gamma,\delta\in\mathbb F_2\}
\]
be its matching column laws. All languages below use the complete normalized-support convention and the fixed final axis-pair set of \(c_0\).

Let a phase word consist of \(J\) consecutive domains, with laws \(X_1,\ldots,X_J\in\mathcal X\), and lengths \(n_1,\ldots,n_J\). Adjacent laws are distinct. Let \(Z_{X_i}(n_i)\) be the protected partition function on that interval, with its actual starting phase.

**Domain-wall bound.** There are absolute \(c,C>0\) such that, for all sufficiently large h and \(n_i\ge Ch\),
\[
 Z_{\mathrm{domains}}(n_1,\ldots,n_J)
 \le e^{-ch(J-1)}
       \prod_{i=1}^J Z_{X_i}(n_i).
\tag{1}
\]
The constants are uniform over the protected row law and the domain laws. The complete proof has passed [independent review](domain_wall_independent_audit.md).

## 1. Three-black supports crossing one wall

Put one wall between columns 0 and 1, with old law \(X_-\) on the left and \(X_+\ne X_-\) on the right. Use tilted rectangles with primitive positive direction \((a,b)\), \(a,b\asymp R\), and side vectors
\[
 u=k(a,b),\qquad v=\ell(-b,a),
\]
where k and \(\ell\) are positive multiples of four. Choose the scales so that both vertical and horizontal side components are at most \(h/10\).

All four rectangle corners have the same coordinates modulo four. Choose the vertical translation so that they belong to the old protected pattern. Translate horizontally so that its rightmost corner W lies to the right of the wall, and the other three corners lie to its left. Restrict to the columns of W on which \(X_-(x)\ne X_+(x)\). Distinct matching laws disagree on at least half of the residues modulo four.

Then W has the wrong row color for its new column phase. Prescribing the other three black corners gives a singleton presentation with an axis rival. The required black cells all lie in the old domain. The new domain is used only to determine the color of W.

The horizontal translation interval has length
\[
 \min(ka,\ell b).
\tag{2}
\]
For each dyadic \(R\le h/C_0\), choose \(a,b\in[R,2R]\) primitive and
\[
 k,\ell\in[h/(100R),h/(50R)]\cap4\mathbb Z.
\]
After a harmless change of the numerical constants, this gives \(\Omega(R^2)\) directions and \(\Omega(h^2/R^2)\) scale pairs. The vertical span is at most \(h/5\), so there are \(\Omega(h)\) allowed vertical translates. Equation (2) gives \(\Omega(h)\) horizontal translates, even after the disagreement-residue restriction. Thus each of \(\Theta(\log h)\) dyadic ranges gives \(\Omega(h^4)\) supports.

Discard \(ka=\ell b\), which would repeat two corner columns. Since \((a,b)=1\), these equalities have \(k=bt,\ell=at\). They contribute only \(O(h)\) scale/direction pairs per dyadic range, compared with \(\Omega(h^2)\) retained pairs. The three black points determine their right triangle and missing corner, so there is no unbounded multiplicity.

Consequently the family R at one wall has
\[
 |R|=\Omega(h^4\log h).
\tag{3}
\]
Its supports lie within an absolute constant times h of the wall. The full comparable-direction family has \(O(h^4\log h)\) such supports as well.

Each event prescribes three row choices, so under the protected product alphabets
\[
 \mu_R=\sum_{E\in R}\Pr(E)=\Theta(h\log h).
\tag{4}
\]

## 2. Overlap bounds in comparable directions

Through any specified black point, the number of rectangles from comparable primitive directions is
\[
 O(h^2\log h).
\tag{5}
\]
Indeed a dyadic direction range contains \(O(R^2)\) choices, and each has \(O(h^2/R^2)\) scale pairs. There are \(O(\log h)\) ranges and only four possible roles for the point.

For two prescribed black points in distinct columns, the third point of a right triangle lies on constantly many perpendicular lines or a Thales circle. Their strip intersections contain \(O(h)\) integer points. A perpendicular line is not horizontal because the two prescribed columns are distinct. A circle has at most two points in each row. Hence
\[
 \#\{\text{compatible supports through two fixed cells}\}=O(h).
\tag{6}
\]
Three fixed black cells determine the event. Deduplicate identical events.

It follows that, after conditioning on one event, compatible events sharing one or two prescribed black cells have total conditional probability respectively
\[
 O(\log h),\qquad O(1).
\tag{7}
\]
Also the total unconditioned event probability incident to a fixed column is \(O(\log h)\): sum (5) over its \(h\) possible rows and multiply by \(O(h^{-3})\).

## 3. Thin the wall family and condition on the domain bulk

For each event of R introduce an independent Bernoulli mark with probability
\[
 \theta=b/\log h,
\]
where b is a sufficiently small absolute constant. Use the marked event, requiring both its three row assignments and its mark. Avoidance of all genuine singleton rivals implies avoidance of this marked family.

Let B contain the complete protected four/six families inside the separate domains. These families use disjoint column sets across domains. Their avoidance count is exactly
\[
 \prod_i Z_{X_i}(n_i).
\tag{8}
\]

Use one marked wall family in the final \(O(h)\) columns of each nonfinal domain. The assumption \(n_i\ge Ch\) ensures that every completion lies in the following domain, and that different wall families have disjoint free-variable neighborhoods.

The total incident marked-event weight is \(O(b)\). The old bulk contributes \(O_\epsilon(h^{-1+\epsilon})\). With \(x_E=2\Pr(E)\), the combined shared-variable local-lemma criterion therefore holds after choosing b small.

Condition on a marked rooted event. Equations (5)--(7) bound the compatible marked-neighbor conditional mass by \(O(b)\). Protected bulk extensions through one, two, or three prescribed black cells contribute \(O_\epsilon(h^{-1+\epsilon})\), by the established support-overlap bounds. Distinct wall families have no shared free columns.

The arbitrary-event conditional local-lemma argument from [relative_sparse_defect_pressure.md](relative_sparse_defect_pressure.md), Section 1, now gives
\[
 \Pr(E\mid\text{avoid any previously listed events})
 \ge \Pr(E)/2
\tag{9}
\]
for every marked wall event, when the bulk is listed first. The mark introduces no extra overlap because each mark belongs to only its own event.

By (4), each wall has total marked mean at least \(c h\). Listing the marked events after B gives
\[
 \Pr(\text{avoid all marked wall events}\mid\text{avoid B})
 \le e^{-ch(J-1)}.
\tag{10}
\]
Multiplying by the protected product-space size and using (8) proves (1).

## 4. What this comparison does and does not give

The event supports proving (1) have width \(O(h)\), rather than the full \(O(h^2)\) sea memory. Thus a protected-phase change has a substantial local pressure cost even when neighboring domains are much shorter than that memory.

For an exact spectral comparison, write
\[
 b_X(n)=\log Z_X(n)-n\log\rho_X,\qquad
 \rho_{\max}=\max_X\rho_X.
\]
Equation (1) implies
\[
 \log Z_{\mathrm{domains}}
 \le m\log\rho_{\max}
    +\sum_i b_{X_i}(n_i)-ch(J-1).
\tag{11}
\]
The existing uniform bound on \(b_X(n)\) is only
\[
 O\!\left(L(\log h)^4/h\right),
 \qquad L=O(h^2).
\]
It is too large to cancel against the wall penalty in (11). In particular, (1) alone does not prove strict component dominance or canonical capture for arbitrary domain profiles. A sharper relative boundary estimate, or a direct bridge preserving the core entropy, is still needed.

