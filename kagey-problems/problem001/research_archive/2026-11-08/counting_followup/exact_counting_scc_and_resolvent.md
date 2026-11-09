# Exact counting by marked transitions and critical components

Research note, 8 November 2026. This gives unconditional finite-state counting statements and a precise replacement for Appendix A of the 7 November REPORT.md. The paper already proves rationality at fixed height. The additional points here are an explicit marked resolvent, exact treatment of hidden rectangles, residue-wise asymptotics, and an algorithmic criterion for the polynomial exponent.

Fix \(h\ge4\), write \(q=\lfloor h^2/4\rfloor\), and fix an unordered balanced bipartition \(\pi\), with edge set \(E_\pi\) and pair set \(F_\pi\). Let \(b_\pi(m)\) count valid words with singleton columns and each edge of \(E_\pi\) occurring exactly once as a double. Beyond the paper's threshold,
\[
 a_h(m)=\sum_\pi b_\pi(m).
 \tag{1}
\]
Different partitions do not double-count a completed word: its complete bipartite double graph determines its unordered bipartition.

## 1. The hidden-rectangle observation

The following observation is proved independently in the companion note on hidden rectangles and thresholds.

**Lemma.** In a valid blackout, a hidden tilted rectangle must have both diagonals parallel to the coordinate axes.

**Proof.** Suppose one black diagonal is \(A=(x,a),C=(z,c)\), with \(x\ne z,a\ne c\). Put \(U=(x,c),V=(z,a)\), and let \(B,D\) be the other black diagonal. The pairs \(U,V\) and \(B,D\) have the same midpoint and length. They give a nondegenerate rectangle \(R'\), unless the original rectangle was axis-aligned. The axis-aligned rectangle \(T=\{A,C,U,V\}\) satisfies
\[
 C(R')\triangle C(T)=\{A,B,C,D\}\subseteq S.
\]
All crossed points remain inside the original bounding box. The two distinct rectangles therefore have equal presentations, a contradiction. \(\square\)

The remaining geometry is a square diamond
\[
 (x-d,y),\ (x+d,y),\ (x,y-d),\ (x,y+d).
\]
If \(d\ge2\), subdivide the perpendicular connector between a pair of opposite sides at its first interior lattice step. The rectangles joining that common intermediate side to the two outer sides have symmetric difference equal to the original four black corners. Their presentations coincide. Thus only \(d=1\) is possible. The full proof is in [hidden_rectangles_and_threshold.md](hidden_rectangles_and_threshold.md).

Its central column contains two black points at row distance two. Consequently:

* A valid sea word has no hidden rectangle, for any partition.
* A valid equality word for the parity partition has no hidden rectangle.
* For another partition, any possible hidden rectangle is completed in the column immediately after its central double. It cannot occur as an independent defect deep inside a sea segment.

Hidden unit diamonds, when allowed, must still be counted globally because validity permits at most one.

## 2. An exact local automaton

Put \(L=2W_h\). Keep the last at most \(L\) column letters over
\[
 \mathcal A_\pi=\{1,\ldots,h\}\cup E_\pi.
\]
When appending a letter, reject a transition if it completes:

1. a tilted presentation of one or two points with an axis-aligned rival, computed using the final pair set \(F_\pi\);
2. two distinct tilted rectangles with the same nonempty presentation.

These tests are local. A tilted rectangle spans at most \(W_h\), and two tilted rectangles with a common shown point have union span at most \(2W_h\). Distinct presentations with three or more points cannot collide.

Reject a transition creating a nonunit hidden rectangle, by section 1. Count the unit diamonds that become hidden at the new rightmost column. Each is counted exactly once. Record whether zero, one, or at least two are newly hidden. The global rule is that at most one can be hidden in total. Axis-aligned collisions are automatic once the double labels are distinct and form \(F_\pi\).

There are two equivalent implementations:

* Add the used-edge subset \(U\subseteq E_\pi\) and a hidden count \(b\in\{0,1\}\) to the state. Reject repeated edges or a hidden count exceeding one. Accept only \(U=E_\pi\).
* Use square-free formal markers, as follows.

On the local-history state space, define nonnegative matrices:

\[
\begin{array}{ll}
 T &: \text{singleton transitions creating no hidden rectangle},\\
 H &: \text{singleton transitions creating exactly one},\\
 E_e &: \text{double \(e\) transitions creating none},\\
 J_e &: \text{double \(e\) transitions creating exactly one}.
\end{array}
\]

Transitions creating at least two newly hidden rectangles are discarded. Work in the commutative ring with \(x_e^2=0\) and \(y^2=0\), and put
\[
 M=T+yH+\sum_{e\in E_\pi}x_e(E_e+yJ_e).
\]
If \(\alpha\) selects the empty history and \(\beta\) accepts every terminal local history, then the exact series is
\[
 F_\pi(z):=\sum_{m\ge0}b_\pi(m)z^m
 =[\textstyle\prod_e x_e]\,([y^0]+[y^1])\,
 \alpha(I-zM)^{-1}\beta.
 \tag{2}
\]
This is an exact coefficient identity. It does not require a choice of overlapping insertion windows.

Write \(R(z)=(I-zT)^{-1}\). Expanding the nilpotent part of the resolvent gives a finite sum of three kinds:

* each of the \(q!\) orders of the \(q\) matrices \(zE_e\), separated by \(R\);
* each order of those matrices and one additional \(zH\), separated by \(R\);
* an order of \(q\) double matrices with one \(zJ_e\) replacing \(zE_e\).

The matrices count words deterministically; permutations indicate the actual chronological order of the labels. Thus the decomposition is unambiguous, including adjacent doubles.

For the parity partition the hidden lemma allows every hidden transition to be rejected outright. The exact formula reduces to
\[
 F_{\rm par}(z)=
 \sum_{\sigma\in\mathfrak S_q}
 \alpha R(z)\,zE_{\sigma(1)}R(z)\cdots
 zE_{\sigma(q)}R(z)\beta.
 \tag{3}
\]

## 3. All exponential rates come from sea components

Every recurrent component of \(T\) consists of full-length singleton histories. A history containing a double is flushed after at most \(L\) singleton steps. A cyclic singleton history cannot retain a hidden rectangle, since going around the cycle would create another copy, which \(T\) forbids. Therefore the nonzero spectrum of \(T\) is exactly that of the hidden-free sea transfer graph, with possible additional zero eigenvalues from transient histories.

The same description applies to the recurrent components of the used-edge/hidden-counter automaton \(A_\pi\). On a cycle, neither the used-edge subset nor the hidden count can increase. After flushing memory, each recurrent component is a copy of a sea component.

Consequently every pole of \(F_\pi\) lies at \(1/\lambda\), for a nonzero sea eigenvalue \(\lambda\). Finite defects can change accessibility and polynomial factors; they cannot introduce a new exponential base.

In particular there are algebraic coefficients and polynomials \(P_{\pi,\lambda}\) such that, for all sufficiently large \(m\),
\[
 b_\pi(m)=\sum_{\lambda\ne0}P_{\pi,\lambda}(m)\lambda^m.
 \tag{4}
\]
The sum is finite. Some polynomials vanish. Zero eigenvalues contribute only finitely many initial terms. This is unconditional and does not assert primitivity, insertion, or parity dominance.

## 4. The exact residue-wise leading term

Trim \(A_\pi\) to states that lie on a start-to-accept path. Let \(p\) be a common multiple of the periods of all its recurrent strongly connected components. For each \(0\le r<p\), consider
\[
 b_\pi(pn+r)=\alpha A_\pi^r(A_\pi^p)^n\beta.
\]
Trim again using the start vector \(\alpha A_\pi^r\). Every recurrent component of this new matrix is primitive.

Let \(R_{\pi,r}>0\) be the largest component spectral radius in that trimmed \(A_\pi^p\) graph. Call a component critical if its radius equals \(R_{\pi,r}\). Let \(\ell_{\pi,r}\) be the largest number of critical components along a start-to-accept path in the condensation graph. Then
\[
 b_\pi(pn+r)
 =c_{\pi,r}n^{\ell_{\pi,r}-1}R_{\pi,r}^{\,n}
 \bigl(1+O(1/n)\bigr),\qquad c_{\pi,r}>0.
 \tag{5}
\]
If a residue has only finitely many accepted words, its sequence is eventually zero instead. Here the paper's alternating-sea construction supplies words at every sufficiently large width, so every residue is nonempty eventually.

**Proof of the exponent rule.** Put the matrix into upper block triangular form by its strongly connected components. A resolvent entry is a finite sum over paths in the condensation graph. Each critical primitive block contributes a simple Perron pole, with a positive rank-one residue. Subcritical block resolvents are analytic and nonnegative at the critical positive singularity. A path visiting \(\ell\) critical blocks contributes a pole of order \(\ell\). Positivity prevents cancellation on a useful path. The largest such order is therefore \(\ell_{\pi,r}\), and coefficient extraction gives (5). \(\square\)

This is an effective criterion:
\[
 \text{the polynomial exponent in residue \(r\) is \(q\)}
 \quad\Longleftrightarrow\quad
 \ell_{\pi,r}=q+1.
 \tag{6}
\]
It is stronger than an informal insertion condition because accessibility, endpoint restrictions, periodicity, and hidden rectangles are already included.

Apply the same procedure to the block diagonal union of the partition automata to obtain (5) for \(a_h(m)\). In each residue, first maximize the exponential base, then the polynomial exponent. The leading constants of tied partitions add. A periodicity hypothesis cannot be omitted by assuming one partition or one component dominates.

## 5. A valid general polynomial upper bound

Let \(\rho_\pi\) be the largest sea-component radius, and let \(k_\pi\) be the largest number of radius-\(\rho_\pi\) sea components on one sea path. Then
\[
 b_\pi(m)=O\left(m^{(q+1)k_\pi-1}\rho_\pi^m\right).
 \tag{7}
\]
The bound can be strict because some globally maximal sea components may not occur on a completed-double path.

There are at most \(q+1\) sea stretches separated by the \(q\) double columns. Each stretch can traverse at most \(k_\pi\) critical sea components. A hidden rectangle does not create an additional stretch: it involves a double and is completed before that double's history has been flushed. Equivalently, the critical-component chain in the exact automaton has length at most \((q+1)k_\pi\).

Algebraically, the identities in (9a) give \(RH=H\) and \(RJ_e=J_e\). Every term in (2) therefore has at most \(q+1\) genuine resolvent factors. In particular a denominator for \(F_\pi\) is
\[
 \det(I-zT)^{q+1}.
\]
At a nonzero eigenvalue whose largest sea Jordan block has size \(s\), the pole order is at most \((q+1)s\).

The bound \(m^{q+k_\pi-1}\rho_\pi^m\) in the earlier report does not follow from the stated hypotheses. A marked double can return from a later sea component to an earlier one, allowing another full critical chain. For an abstract transfer example, take
\[
 T=\begin{pmatrix}2&1\\0&2\end{pmatrix},\quad
 E=\begin{pmatrix}0&0\\1&0\end{pmatrix},\quad
 \alpha=(1,0),\quad\beta=(0,1)^T.
\]
Then
\[
 \alpha R(z)\,zE\,R(z)\beta
 =\frac{z^3}{(1-2z)^4}.
\]
There is one marker and two critical sea components, but the polynomial degree is three rather than two. This is a counterexample to that general transfer inference, not an exhibited blackout counterexample. A better bound for blackout graphs would need an additional structural theorem.

## 6. The product formula, with precise hypotheses

Suppose \(T\) has a unique dominant component, it is primitive, and its Perron root is \(\rho\). The eigenvalue \(\rho\) is then simple even if \(T\) is reducible. Choose nonnegative right and left eigenvectors \(v,u\), and write
\[
 \Pi=\frac{vu}{uv},\qquad
 B=\alpha\Pi\beta,\qquad
 \kappa_{e,0}=\frac{uE_ev}{\rho\,uv}.
\]
For hidden-free words, (3) and the rank-one identity
\[
 R(z)=\frac{\Pi}{1-\rho z}+K(z)
\]
give, if all \(\kappa_{e,0}>0\),
\[
 b_{\pi,0}(m)
 =B\left(\prod_e\kappa_{e,0}\right)m^q\rho^m
 \bigl(1+O(1/m)\bigr).
 \tag{8}
\]
Every order has the same leading residue. The \(q!\) orders cancel the \(1/q!\) from extracting the order-\(q+1\) pole. This proof uses the exact one-letter marked operators on the extended history space, so close doubles and the lengths of insertion windows cause no ambiguity.

For parity equality words, all valid words are hidden-free. Thus (8) is the full counting formula whenever the unique dominant component has positive insertion weights.

### The nonparity hidden correction

The left Perron vector \(u\) is supported on states reachable from a recurrent pure-sea component by singleton transitions. Those states contain no doubles. Hence
\[
 uH=0,\qquad uJ_e=0,\qquad \alpha R(z)H=0.
 \tag{9}
\]
Indeed a possible hidden diamond must be completed strictly after its central double. It cannot be created by singleton transitions from a pure sea, or by the first double itself.

In fact the unit-diamond classification gives the stronger identities
\[
 TH=TJ_e=0,\qquad R(z)H=H,\qquad R(z)J_e=J_e.
 \tag{9a}
\]
After a singleton transition, the preceding column is a singleton. The next column cannot then complete a hidden unit diamond, whose central column must be a double. Define
\[
 \kappa_{e,1}=\frac{uE_eHv}{\rho^2uv}.
 \tag{10}
\]
This is the weight of an isolated insertion of \(e\) that creates one hidden diamond in the next singleton column. It vanishes unless \(e=\{r-1,r+1\}\) for some row \(r\).

In the terms with one \(H\), it cannot precede the first double. Combine it with the immediately preceding double marker. The identity \(RH=H\) forces the hidden completion to occur in the next column, so that combined insertion uses one long-gap position. Terms with \(J_e\) require an immediately preceding double and lose at least one Perron pole. Consequently the full leading coefficient at degree \(q\) is
\[
 C_\pi
 =B\,([y^0]+[y^1])\prod_{e\in E_\pi}
       (\kappa_{e,0}+y\kappa_{e,1}).
 \tag{11}
\]
If \(C_\pi>0\), then
\[
 b_\pi(m)=C_\pi m^q\rho^m(1+O(1/m)).
\]
If \(C_\pi=0\), the degree at exponential base \(\rho\) is at most \(q-1\), or that base is inaccessible altogether.

This correction is needed for arbitrary partitions unless hidden diamonds have been excluded separately. For parity, every \(\kappa_{e,1}=0\), and (11) reduces to (8).

## 7. An unconditional lower bound for every partition

The companion note [insertion_adjacent_component.md](insertion_adjacent_component.md) proves that the single-switch seas \(1^\infty h^\infty\) and \(h^\infty1^\infty\) are valid for every pair set \(F_\pi\). Hence the two boundary constant states belong to one primitive component \(C_{\pi,*}\). The isolated-double boundary-sea construction inserts every edge of \(E_\pi\) from one state of this component to another. Write its radius as \(\rho_{\pi,*}\).

It follows unconditionally that
\[
 b_\pi(m)\ge c_\pi m^q\rho_{\pi,*}^m
 \tag{12}
\]
for all sufficiently large \(m\), for every balanced partition. Fix an edge order and fixed insertion bridges. Primitivity gives a positive multiple of \(\rho_{\pi,*}^n\) sea paths between each prescribed pair of bridge endpoints. Sum over the \(q+1\) sea-path lengths. Double positions make the decomposition unambiguous.

In every partition, \(\rho_{\pi,*}>1\). One explicit bound is \(2^{1/L}\): concatenate arbitrary blocks \(1^L\) and \(h^L\). A forbidden window has length at most \(L+1\), while seeing two switches separated by a run of length \(L\) needs at least \(L+2\) columns. Thus every such block word is valid.

When \(h\) is even, the full boundary alphabet \(\{1,h\}\) is a valid two-shift for every partition, so \(\rho_{\pi,*}\ge2\) for every \(\pi\). A weak tilted rectangle has its black diagonal in the boundary rows; a horizontal white diagonal would have nonintegral midpoint row, a vertical one would leave the grid, and oblique rivals and repeated presentations are excluded by the boundary geometry.

For parity, every adjacent-row alphabet is a full sea two-shift. Therefore \(C_{{\rm par},*}\) contains every constant state and \(\rho_{{\rm par},*}\ge2\). Consequently
\[
 a_h(m)\ge c_hm^q\rho_{{\rm par},*}^m\ge c_hm^q2^m.
\]

The insertion issue is therefore solved on an explicit primitive component for every partition. If \(C_{\pi,*}\) is its unique dominant sea component, the insertion hypothesis in section 6 is automatic. Parity then has the uncorrected product (8); another partition has the possible diamond correction (11). Dominance of these components and dominance among partitions remain separate questions.

## 8. Error terms and limitations of the earlier formulation

Under the unique primitive hypothesis, the exact expansion has the form
\[
 b_\pi(m)=\rho^mP_\pi(m)
          +O(m^D(\rho')^m),
 \tag{13}
\]
where \(\rho'<\rho\) is the largest modulus of any remaining contributing eigenvalue, and \(D\) is determined by the pole orders there. If that remainder spectrum is empty, the remainder is eventually zero.

The degree \(D\) is not automatically at most \(q\). Subdominant sea eigenvalues can have nontrivial Jordan blocks, and marked products can increase their pole orders. A convenient safe alternative is
\[
 b_\pi(m)=\rho^mP_\pi(m)+O(\theta^m)
 \quad\text{for every }\rho'<\theta<\rho.
 \tag{14}
\]
For both hidden-free and full counts, a sea Jordan block of size \(s\) gives the crude subdominant pole-order bound \((q+1)s\). The exact finite automaton or marked resolvent determines sharper bounds.

The main corrections to Appendix A are therefore:

* rationality and finite exponential-polynomial expansions are unconditional;
* the exact exponent is a useful critical-component chain length minus one, after accounting for periods;
* the general reducible upper-bound degree is \((q+1)k_\pi-1\), unless additional structure improves it;
* hidden rectangles are impossible for parity equality words, so they do not obstruct its product formula;
* arbitrary partitions require the diamond correction or the exact hidden counter;
* subdominant error terms need their own pole-multiplicity bound;
* dominance among partitions and dominance of each boundary component \(C_{\pi,*}\) remain separate mathematical questions.
