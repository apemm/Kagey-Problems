# Continuation: the sign of a common-alphabet surface comparison

9 November 2026. Changing r rows can change a full interface factor by order rh, even when the two models have identical permitted black alphabets. In the controlled comparison below, the change has the favorable sign: the new row constraints make the interface factor smaller.

This distinguishes the target needed for exact optimality from an absolute Lipschitz bound. A bound on possible interface improvement could still hold. An absolute \(O(r\log^2h)\) bound does not hold in this model.

Fix a quadratic protected row/column pair \((c_0,X)\). Let c be a balanced row law that differs from c_0 on E, with
\[
 1\le r=|E|\le h^{1/4}.
\tag{1}
\]
The reference c_0 may have the harmless class-size imbalance two. In both models use the same column alphabets
\[
 A_x=\{y\in[1,h]\setminus E:c_0(y)=X(x)\}.
\tag{2}
\]
These alphabets have size \(h/2+O(r)\), are periodic with period dividing four, and contain no changed black row.

Let \(Z_0(I)\) and \(Z_1(I)\) be the normalized fixed-final-F partition functions on an interval I, using final partitions c_0 and c respectively and the common alphabets (2). For adjacent intervals \(I_-,I_+\), define the exact interface factors
\[
 {\cal I}_j(I_-,I_+)
 =\log Z_j(I_-\cup I_+)
   -\log Z_j(I_-)-\log Z_j(I_+),
 \qquad j=0,1.
\tag{3}
\]
All constraints are normalized by their required black support. In particular, a common white corner may lie outside I.

**Theorem.** There are absolute \(a,C>0\) such that, for large h and both interval lengths at least the complete support memory \(L_h=O(h^2)\),
\[
 -Crh
 \ \le\
 {\cal I}_1(I_-,I_+)-{\cal I}_0(I_-,I_+)
 \ \le\
 -arh.
\tag{4}
\]
The bounds are uniform in the lengths, the cut phase, and E.

The theorem concerns one fixed matched phase and the common alphabets (2). It does not compare the full alphabets under c and c_0, or a wall between different matched phases. Those remain the missing cases for exact quadratic optimality.

## 1. The additional constraints are explicit

Let B be the deduplicated canonical protected four/six support family, restricted to the alphabets (2). It consists of hidden, mixed, and genuine six-cell supports. Remove redundant supports containing an already forbidden smaller support.

For c_0, B is the complete constraint family. Protected row/column laws automatically prevent singleton axis rivals and vertical-pair axis rivals.

For c, there are only two additional types.

- T consists of three-black tilted rectangles whose completion row belongs to E and whose old completion color agrees with X at its column.
- V consists of complementary black diagonals of vertical displayed pairs whose two row colors become different under c. Exactly one displayed endpoint is in E.

Both types are genuinely forbidden independently of the letter at the completion or displayed midpoint column. Every required black row remains outside E.

If both displayed endpoints of a vertical pair belong to E, both colors flip and no new rival appears. There are no other changes, because every selected black row has the same color in c and c_0.

Deduplicate V. Delete T supports containing a V support. Finally delete B supports containing either a retained T support or a V support. Write the remaining bulk as \(B^\sharp\), and put
\[
 {\cal F}_1=B^\sharp\cup T^\sharp\cup V.
\tag{5}
\]
This is a minimal positive-support description of the new model. Deleting redundant constraints leaves its partition function unchanged.

## 2. Uniform conditional probabilities

For a canonical event A and any subfamily S not containing it, the conditional local-lemma argument gives
\[
 \Pr(A\mid \text{avoid }S)=\Pr(A)(1+O(\theta_h)),
\tag{6}
\]
uniformly in S, where one may take
\[
 \theta_h=C_\eta\bigl(rh^{-1/2}+h^{-1+\eta}\bigr)
\tag{7}
\]
for any fixed small positive eta.

Here are the required estimates.

The bulk has raw incident and compatible extension weight \(O_\eta(h^{-1+\eta})\), by the canonical four/six codegree table. Those geometric bounds do not require a particular permitted row subset; the lower bound \(|A_x|\ge h/3\) suffices.

For T, one fixed black cell and a prescribed completion row give \(O_\eta(h^{1+\eta})\) rectangles. Two fixed black cells and a prescribed completion row give O(1): the completion lies on a circle or one of finitely many nonhorizontal perpendicular lines. A horizontal completion line would require the two fixed black cells to share a column. Thus the compatible one-/two-cell extension weights are
\[
 O_\eta(rh^{-1+\eta})+O(r/h).
\]
Its raw incident weight is \(O(r\log^2h/h)\).

For V, fix a black endpoint with row a and a changed displayed endpoint with row w. If the other black row is b, the equal-diagonal equation is
\[
 d_x^2=4(a-w)(b-w).
\tag{8}
\]
Both a-w and b-w are nonzero. Their squarefree kernels must agree, so there are at most \(C\sqrt h\) choices for b and two horizontal signs. The compatible one-cell weight is therefore \(O(r/\sqrt h)\). The raw weight is no larger.

All identical events are deduplicated. Containments have been removed in (5), so two distinct events cannot share all assignments of the smaller event. These facts prove (7).

For clarity, (6) uses two bounds. The arbitrary-event conditional local-lemma inequality gives the upper bound
\(\Pr(A\mid\operatorname{avoid}S)\le\Pr(A)(1+O(\theta_h))\).
For the lower bound, separate S into events independent of A and its neighbors. After prescribing A, the sum of compatible residual probabilities of its neighbors is \(O(\theta_h)\). The conditional union bound used in the exact pressure notes then gives the lower bound \(1-O(\theta_h)\).

Equation (1) makes theta_h tend to zero. The original bulk B separately satisfies the same estimate with \(O_\eta(h^{-1+\eta})\).

## 3. Interface factors are crossing means with a small relative error

For a constraint family F, first avoid all events supported wholly in either half. The two sets of variables are independent. Then list every crossing event. Equation (6) gives
\[
 {\cal I}_{\cal F}
   =-\mu_{\cal F}^{\rm cut}
       +O(\theta_h\mu_{\cal F}^{\rm cut}),
\tag{9}
\]
where
\[
 \mu_{\cal F}^{\rm cut}
   =\sum_{\substack{A\in{\cal F}\\
             \operatorname{supp}(A)\text{ crosses the cut}}}\Pr(A).
\]
The quadratic correction in \(\log(1-p)\) is absorbed into the displayed error.

The interval lengths at least L_h ensure that every possible crossing support appears. Its mean depends only on the cut phase, rather than the lengths of the two halves.

The old bulk crossing estimate is
\[
 \mu_B^{\rm cut}\le Ch\Lambda^2,\qquad \Lambda=1+\log h.
\tag{10}
\]
For all three-black rectangles with a fixed completion row w, the full span sum is \(O(h^4)\). Consequently
\[
 \mu_T^{\rm cut}\le Crh.
\tag{11}
\]
For V, a displayed vertical pair has length at most h. For each changed endpoint row there are h choices of the other endpoint and \(O_\eta(h^\eta)\) integer alternate diagonals. Its black span is at most h. Hence
\[
 \mu_V^{\rm cut}\le C_\eta rh^\eta.
\tag{12}
\]

## 4. A lower bound of order h per changed row

Fix \(w\in E\), and choose the vertical sign epsilon toward the farther boundary. For
\[
 h/200\le b,l\le h/100
\]
take a completion \(W=(x,w)\) and perpendicular sides
\[
 U=(4,4\epsilon b),\qquad
 V=(-4lb,4\epsilon l).
\tag{13}
\]
The three black points are \(W+U,W+V,W+U+V\). All rows fit in the strip. Their columns are distinct. Every coordinate difference is divisible by four, so all three black cells obey the reference protected law whenever W has the old selected color.

There are \(\Theta(h^2)\) pairs (b,l). Excluding a black row in E removes only \(O(rh)\) pairs: each such equality fixes b, l, or b+l. Thus a fixed positive fraction survives uniformly in (1).

These three-cell supports contain no V event. The short side has length
\[
 4\sqrt{1+b^2},
\]
which is not an integer. It cannot have an integral vertical displayed alternative. The other two black pairs have horizontal displacement \(\Theta(h^2)\), exceeding the maximum length h of an in-strip vertical displayed pair.

Each surviving support has span \(\Theta(h^2)\). It therefore has \(\Theta(h^2)\) translations crossing a fixed cut with the required period-four completion phase. Its event probability is \(\Theta(h^{-3})\). The black triple determines W uniquely, and its side with horizontal displacement four distinguishes the parameters, so multiplicity is bounded.

Summing over b,l and w gives
\[
 \mu_{T^\sharp}^{\rm cut}\ge crh.
\tag{14}
\]
This is the source of the large surface change. Its bulk mean per column is only order \(r/h\); the large contribution to the interface comes from its order-\(h^2\) span.

## 5. Redundant old bulk contributes only a lower-order correction

It remains to bound the crossing weight of \(B\setminus B^\sharp\). Use the geometric codegrees
\[
 M_{4,2}\le C_\eta h^{1+\eta},\quad
 M_{4,3}\le C_\eta h^\eta,\quad
 M_{6,2}\le C_\eta h^{3+\eta},\quad
 M_{6,3}\le C_\eta h^{2+\eta}.
\tag{15}
\]
There are \(O(rh^2\Lambda^2)\) normalized T supports, and
\(O_\eta(rh^{1+\eta})\) normalized V supports. Each extension to a bulk support has at most \(Ch^2\) cut translations.

Multiplying by the corresponding four- or six-cell probability yields
\[
 \mu_{B\setminus B^\sharp}^{\rm cut}
 \le C_\eta r h^{2\eta}\Lambda^2=o(rh).
\tag{16}
\]
This deliberately overcounts supports containing more than one smaller constraint. It avoids any assumption that a full geometric witness has bounded multiplicity.

Combining (10)--(16),
\[
 crh-o(rh)
 \le
 \mu_{{\cal F}_1}^{\rm cut}-\mu_B^{\rm cut}
 \le Crh.
\tag{17}
\]

Finally, the conditional errors in (9) are \(o(rh)\). Indeed, for a fixed sufficiently small eta,
\[
 \theta_h(h\Lambda^2+rh)
 \le C_\eta\left(
       r\sqrt h\,\Lambda^2+r^2\sqrt h
       +h^\eta\Lambda^2+rh^\eta
      \right)
 =o(rh)
\]
uniformly in (1). Equations (9) and (17) prove (4).

## 6. What this resolves, and what it does not

The common-alphabet comparison retains the newly forbidden row-root constraints across the interface. Their contribution is favorable and much larger than \(r\log^2h\). Deleting them at a cut would therefore lose useful information.

A route to full exact optimality should bound the *positive* change of an interface weight. It should not seek an absolute \(O(r\log^2h)\) estimate for all changed constraints.

The remaining terms are concrete. Restoring changed black letters changes the local product space. A wall between different matched phases also has pre-existing singleton and vertical constraints whose conditional interaction with the new row roots is not covered by the protected bulk lemma. Equation (4) proves neither of those comparisons.

The complete crossing-probability comparison passed [independent review](common_alphabet_surface_independent_audit.md).

