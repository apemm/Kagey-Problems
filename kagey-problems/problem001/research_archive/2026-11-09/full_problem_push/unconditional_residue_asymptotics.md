# An unconditional asymptotic on width residue classes

9 November 2026. Finite nonnegative transfer matrices give a general
asymptotic without any component-dominance assumption. The resulting
parameters remain spectral and algorithmic. This does not identify them
in a simpler height-dependent form.

Fix \(h\ge4\), put \(q=\lfloor h^2/4\rfloor\), and let \(a_h(m)\) count
optimal identifying blackouts on the labeled \(h\)-by-\(m\) grid.

**Theorem.** There is an effectively computable positive integer \(p_h\).
For every \(r\in\{0,\ldots,p_h-1\}\), there are a positive real algebraic
integer \(R_{h,r}\), a nonnegative integer \(d_{h,r}\), and a polynomial
\(P_{h,r}\) with real algebraic coefficients and positive leading
coefficient, such that
\[
 a_h(m)=R_{h,r}^{\,m}P_{h,r}(m)+O(\theta_{h,r}^{\,m})
 \quad(m\longrightarrow\infty,\ m\equiv r\pmod {p_h}),
 \tag{1}
\]
where \(0<\theta_{h,r}<R_{h,r}\) and
\(\deg P_{h,r}=d_{h,r}\). In particular,
\[
 a_h(m)\sim C_{h,r}m^{d_{h,r}}R_{h,r}^{\,m},
 \qquad C_{h,r}>0.
 \tag{2}
\]
All the displayed data admit finite exact algorithms.

The theorem does not assert that \(p_h=1\), that all \(R_{h,r}\) agree,
or that \(d_{h,r}=q\). Those are additional structural conclusions, not
automatic consequences of rationality.

## 1. A nonnegative integer representation

The threshold construction proves
\[
 f(h,m)=m+q
 \qquad(m\ge M_h)
\]
for an effectively bounded \(M_h\). Equality in the axis bound forces
exactly the \(q\) distinct doubles of a balanced complete bipartite row
partition, with every other column a singleton.

For each unordered balanced partition, use the exact finite-end history
automaton from all_width_counting_formula.md. Augment a state by the set
of double labels already used. A singleton transition leaves that set
unchanged. A double transition adds its label and is forbidden if the
label has already appeared. Initial states have the empty history and
empty used set. Accepting states have used every double label.

Take the disjoint union over all unordered balanced partitions, and let
\(A_h\) be its nonnegative integer adjacency matrix. Each letter is
counted once, including when different letters induce the same transition.
Let \(u_h,v_h\) be its nonnegative integer initial and final vectors.
Then
\[
 a_h(m)=u_hA_h^mv_h\qquad(m\ge M_h).
 \tag{3}
\]
The equality family has a unique balanced partition, so this sum has no
duplicate boards. The exact local tests use contained rectangles at the
two ends; normalized residual-graph endpoint conventions cannot be
substituted in (3).

The all-width enumerator provides the finitely many terms below \(M_h\).
Changing finitely many terms changes its width generating function by a
polynomial and has no effect on (1).

## 2. Remove periodicity by taking a matrix power

Discard states that lie on no initial-to-final path. Each recurrent
strongly connected component has an integer period, the gcd of its
directed cycle lengths. Let \(p_h\) be the least common multiple of these
periods. A component consisting of a transient singleton contributes
nothing to this least common multiple.

Every recurrent irreducible diagonal block of \(B=A_h^{p_h}\) is
primitive. To see this, an irreducible component of period d splits into
d cyclic classes. Its d-th power is primitive on each class, and every
further power remains primitive. Distinct original components cannot
merge under powering, because that would create a directed cycle in the
original condensation graph.

For residue r set
\[
 u_r=u_hA_h^r,\qquad b_r(n)=u_rB^nv_h.
 \tag{4}
\]
Trim B again to the states on a \(u_r\)-to-\(v_h\) path. The all-width
construction ensures that \(b_r(n)>0\) for all sufficiently large n.
Consequently this trimmed graph contains a recurrent component.

Let \(\Lambda_r\) be the largest Perron root of its recurrent blocks.
Each such block is primitive, so its only eigenvalue of modulus
\(\Lambda_r\) is the positive real eigenvalue \(\Lambda_r\). Smaller
blocks and transient blocks have smaller spectral radius.

## 3. The pole order is an exact chain invariant

Call a recurrent block critical when its radius is \(\Lambda_r\).
Let \(k_r\) be the largest number of critical blocks on a directed
initial-to-final path in the trimmed B graph. Then
\[
 u_r(I-zB)^{-1}v_h
\]
has a pole of exactly order \(k_r\) at \(z=1/\Lambda_r\).

Indeed, order the components topologically and expand the resolvent
along component paths. A critical diagonal resolvent has a simple
positive Perron residue. Every subcritical diagonal resolvent is
analytic and entrywise nonnegative at \(1/\Lambda_r\). A component path
through \(k\) critical blocks therefore contributes at most a pole of
order k.

For a path attaining \(k_r\), its nonzero connecting matrices, the
strictly positive Perron vectors within the critical blocks, and its
accessible initial and terminal factors make the coefficient of
\((1-\Lambda_r z)^{-k_r}\) strictly positive. Nonnegative component-path
expansions cannot cancel this coefficient. This proves the exact order.

All remaining poles have modulus strictly greater than
\(1/\Lambda_r\). Partial fractions give
\[
 b_r(n)=\Lambda_r^nQ_r(n)+O(\eta_r^n),
 \qquad 0<\eta_r<\Lambda_r,
 \tag{5}
\]
with \(Q_r\) of degree \(k_r-1\) and positive leading coefficient.
Possible polynomial factors at smaller exponential radii are absorbed
by choosing \(\eta_r\) slightly larger than those radii.

The matrix and boundary vectors are integral. Their rational generating
function has algebraic poles and algebraic partial-fraction
coefficients, so \(Q_r\) has real algebraic coefficients.

Set
\[
 R_{h,r}=\Lambda_r^{1/p_h},\qquad
 P_{h,r}(m)=R_{h,r}^{-r}
 Q_r\!\left(\frac{m-r}{p_h}\right).
 \tag{6}
\]
The positive p-th root in (6) is the Perron root of an original
irreducible block of \(A_h\), so it is a real algebraic integer.
Equations (4)--(6) prove the theorem, with \(d_{h,r}=k_r-1\).

## 4. Geometric bounds and the remaining simplification

Every recurrent block of \(A_h\) is a copy of a singleton-sea component:
the used-label set cannot change on a cycle, and a double in the
history disappears after finitely many singleton steps. Thus the
exponential bases in (1) come from unmarked singleton-sea Perron roots, not from
new recurrent marked dynamics.

The deletion lemma in hereditary_marked_bridges.md bounds the number of
critical copies on an accepting path by \(q+k\), where k is the number
of distinct critical underlying sea components on that path. Hence
\[
 d_{h,r}\le q+k-1.
 \tag{7}
\]
This bound can be applied after restricting to the components relevant
to residue r and its radius.

The unconditional collared construction gives a lower bound at every
sufficiently large width. If \(\lambda_h^\partial\) is the largest
boundary-component Perron root over balanced partitions, then
\[
 R_{h,r}\ge\lambda_h^\partial
\]
for every r. When equality holds, the collared degree-q lower bound
also forces \(d_{h,r}\ge q\).

For height seven, the completed component and partition certificates
show that the only maximal components are primitive boundary
components in two reflected partitions. Thus the general form collapses
to one radius, one polynomial of degree twelve, and no residue
dependence. The same collapse at arbitrary height is precisely the
unresolved structural issue.
