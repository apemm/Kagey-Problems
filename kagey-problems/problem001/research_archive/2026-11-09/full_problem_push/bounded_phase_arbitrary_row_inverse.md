# A bounded-period phase forces the row law

9 November 2026. This note proves an aggregate inverse theorem when the column phase has bounded period and the balanced row partition is arbitrary. The argument has passed independent review.

Fix a positive integer P. Let \(t:\mathbb Z\to\mathbb F_2\) have period P, and let \(c_h:[1,h]\to\mathbb F_2\) be any balanced row coloring. Put
\[
 W_h=\{(x,y)\in[h]^2:c_h(y)=t(x)\},
\]
and let \(N_3(W_h)\) count tilted rectangles with exactly three selected corners.

**Theorem.** If
\[
 N_3(W_h)=o(h^4\log h),
\tag{1}
\]
then t is a protected phase,
\[
 t(x)=\kappa q(x)+\gamma x+\delta,\qquad q(x)=\binom x2\bmod2,
\]
and
\[
 \min_{\alpha,\beta}
 \#\{y:c_h(y)\ne\kappa q(y)+\alpha y+\beta\}=o(h),
\tag{2}
\]
where \(\alpha=1\) if \(\kappa=0\).

The statement is uniform over the finitely many phases of period dividing P. In particular, a fixed nonprotected periodic phase has a fixed positive \(h^4\log h\) test density for every balanced row partition once h is sufficiently large.

## 1. A nonconstant phase supplies both complementary tests

Assume first that t is nonconstant. Restrict a rectangle's side vectors to
\[
 Pk(a,b),\qquad Pl(-b,a),
\tag{3}
\]
where \(a,b\) are positive and coprime. All four columns are congruent modulo P, so their column phases are equal.

For fixed row basepoint y and scales k,l, the four row colors have odd XOR exactly when
\[
 c_h(y)+c_h(y+Pkb)+c_h(y+Pla)+c_h(y+Pkb+Pla)=1.
\tag{4}
\]
In this case one of the two constant column phases selects three corners and the other selects one. Both phases occur in t, each on at least one residue modulo P.

Take \(a,b\in[R,2R]\) and
\[
 K=\lfloor\eta h/(PR)\rfloor,\qquad0<\eta<1/100.
\]
For \(1\le k,l\le K\), the horizontal and vertical spans in (3) are at most \(4\eta h\). Thus every failure (4) whose rows fit has at least \(c_Ph\) horizontal translations with exactly three selected corners, for a constant \(c_P>0\).

If \(N_{a,b}\) is the total three-corner count in this primitive direction, the number of failures (4), summed over these k,l and all row basepoints, is at most
\[
 C_P N_{a,b}/h.
\tag{5}
\]

## 2. Each row residue class becomes affine

Use dyadic direction ranges
\[
 h^{1/32}\le R\le h^{1/16}.
\]
As in [the protected-row inverse proof](protected_row_aggregate_inverse.md), (1) implies that in at least one range all but \(o(R^2)\) primitive directions satisfy
\[
 N_{a,b}=o(h^4/R^2),
\tag{6}
\]
with a common vanishing error.

Fix a row residue r modulo P and write
\[
 f_r(n)=c_h(r+Pn)
\]
on its interval of \(h/P+O(1)\) integer indices. For a good direction form the lifted matrix
\[
 G_{ij}=f_r(n_0+bi+aj),\qquad1\le i,j\le K.
\tag{7}
\]
Each odd-XOR matrix rectangle is a failure in (4). A fixed physical row basepoint and pair of scale differences has at most \(K/R+1\) representations, since solutions of \(bi+aj=n-n_0\) differ by \((a,-b)\). Equations (5)--(6) therefore give \(o_{P,\eta}(K^4)\) odd-XOR subrectangles in every such matrix.

Apply the lifted XOR repair from Sections 2--4 of the protected-row inverse proof. It uses only the following facts, which hold here:

- An \(o(K^4)\) odd-XOR count repairs the matrix to \(u_i+v_j\) in \(o(K^2)\) entries.
- The exact overlaps \(G_{i+a,j-b}=G_{ij}\), and all their multiples, make the repaired label increments additive without accumulating errors.
- Central physical rows have at least \(cK/R\) matrix representations.
- Four nearby odd primitive directions
  \((a,b),(a+2,b),(a,b+2),(a+2,b+2)\)
  can all be chosen good, and their approximate periods have gcd two.

Changing j to \(K+1-j\) converts (7) to the sign convention used there. The argument is unchanged. The same four directions work for all P row residues, since (5) bounds their total count.

Consequently every \(f_r\) is \(o(h/P)\)-close to an affine parity law on its index interval. Equivalently, there is a binary \(2P\)-periodic function \(c_h^*\) such that
\[
 \#\{y:c_h(y)\ne c_h^*(y)\}=o(h).
\tag{8}
\]
The finite list of affine choices may depend on h.

## 3. The remaining periodic pair is protected

There are only finitely many \(2P\)-periodic binary functions. Since \(c_h\) is balanced and (8) holds, every \(c_h^*\) occurring for arbitrarily large h must be balanced over one period: its limiting density is \(1/2\), and the finitely many possible period densities are separated.

If a pair \(c_h^*,t\) is nonprotected, [periodic rectangle amplification](periodic_rectangle_amplification.md) gives a positive \(h^4\log h\) three-corner count, uniformly over this finite collection. The amplification may be restricted to comparable primitive directions in the dyadic range used above.

A pattern balanced over its period need not restrict to an exactly balanced partition at every height. If needed, apply the amplification on the largest square whose side is divisible by \(2P\). This discards only \(O(P)\) rows and columns, preserves the asymptotic lower bound, and satisfies the earlier finite-height balance hypothesis literally.

Changing one row changes only \(O(h^3\log h)\) tests in that comparable-direction family; the proof is in Section 4 of [the periodic constant-phase estimate](constant_phase_periodic_amplification.md). Thus the \(o(h)\) row edits in (8) change only \(o(h^4\log h)\) tests. A nonprotected periodic approximation would contradict (1).

Therefore all sufficiently large approximating pairs are protected. This gives (2) and proves that t itself is protected.

If t is constant, instead apply [the constant-phase aggregate inverse](component_permutation_repair.md). It gives (2) with \(\kappa=0\). This completes the proof.

## 4. Uniform entropy gaps across balanced row partitions

Fix a period bound \(P_0\). There are constants \(\eta_{P_0},\gamma_{P_0}>0\) such that, for all sufficiently large h, every balanced row partition c and every nonprotected phase t of period at most \(P_0\) have the following property:

The valid sea words whose phase differs from t in at most \(\eta_{P_0}m\) columns have exponential growth rate at most
\[
 (1/2-\gamma_{P_0})h.
\tag{9}
\]
The changed columns may have arbitrary spacing and arbitrarily large clusters.

To see the uniformity, otherwise a sequence of balanced c and phases from this finite family would have vanishing normalized three-corner count. Pass to one repeated phase and apply the theorem, a contradiction. Hence their full boxes have a common positive test density. Removing the lower-order repeated-column cases and converting to singleton-rival supports gives the uniform edge lower bound required in Section 4 of [the robust entropy-gap argument](bounded_period_entropy_gap.md). That argument proves (9).

For a protected base phase, the same conclusion holds whenever c stays a fixed positive row distance from its matched row laws, by Section 5 of that note.

This is an asymptotic statement uniform over row partitions, with the period bound fixed before h grows. It does not bound profiles whose period grows without limit, and it does not assert a fixed-height dominance theorem.

## 5. A periodic row law controls arbitrary phases

The balance assumption was not used in Sections 1--2. Their intermediate conclusion can be stated symmetrically:

**Fiber-repair lemma.** If one coordinate word is a fixed nonconstant P-periodic word and the aggregate three-corner count is \(o(h^4\log h)\), the other coordinate word is \(o(h)\)-close to a \(2P\)-periodic word. No balance condition is needed for this intermediate conclusion.

Now let c be a fixed row law balanced over a period P, and let \(t_h\) be an arbitrary column word. Assume \(N_3(c,t_h)=o(h^4\log h)\). Transpose the board and apply the fiber-repair lemma: the periodic phase is c, which is nonconstant because it is balanced. It follows that \(t_h\) is \(o(h)\)-close to a \(2P\)-periodic phase \(t_h^*\).

Transpose back. The original row law c is balanced and periodic, so the finite periodic amplification applies to \((c,t_h^*)\). The row/column edit bound again transfers its test count to the original pair. Consequently c must be protected, and \(t_h\) must be \(o(h)\)-close to a matched protected phase.

In particular, if c is a fixed nonprotected balanced periodic row law, there is a constant \(a_c>0\) such that
\[
 N_3(c,t)\ge a_c h^4\log h
\tag{10}
\]
for every column word t and all sufficiently large h. Otherwise a sequence violating (10) would contradict the preceding inverse statement.

The lower bound can be confined to the comparable-direction family with
\(h^{1/32}\le R\le h^{1/16}\) used throughout the proof. Both the fiber repair and the final periodic amplification use only that family, so the same contradiction applies if its restricted count were \(o(h^4\log h)\).

## 6. Full entropy gaps for nonprotected periodic row partitions

Fix a period bound \(P_0\). There is \(\gamma_{P_0}>0\) such that every balanced nonprotected row law c of period at most \(P_0\) has full sea entropy
\[
 \rho_c(h)\le(1/2-\gamma_{P_0})h
\tag{11}
\]
at all sufficiently large admissible heights. There is no restriction on its column-phase profiles.

The finitely many row laws make (10) uniform. Suppose a small-edge container had size \((1/2-o(1))h^2\). Uniform container purification would give a full box \(W(c,t)\) with \(N_3(c,t)=o(h^4\log h)\), contradicting (10). Quantitatively, choose the edge-density threshold sufficiently small. Then every resulting container has size at most \((1/2-\eta_{P_0})h^2\), for some fixed \(\eta_{P_0}>0\). The fingerprint-aware transversal count gives (11).

This gap is stable under a sufficiently small fraction of row changes. More precisely, for each fixed nonprotected balanced periodic base c, there are \(\delta_c,\gamma_c>0\) such that every balanced row coloring \(c_h\) with
\[
 \#\{y:c_h(y)\ne c(y)\}\le\delta_ch
\]
has \(\rho_{c_h}(h)\le(1/2-\gamma_c)h\), for all sufficiently large h.

To verify the transfer, changing one row changes at most \(O(h^3\log h)\) rectangle tests in the comparable-direction family used in (10). The proof of (10) gives its positive lower bound within that family. A small enough \(\delta_c\) therefore preserves a fixed positive test density uniformly in t. Apply purification for the new balanced partition \(c_h\). No identification of the two different singleton hypergraphs is needed.

Since the ordinary canonical component has growth
\[
 \lambda_*(h)\ge h/2-O(\log^4h),
\]
it eventually exceeds all the rates in (11), for each fixed \(P_0\). Hence a maximizing row partition with a uniformly bounded period must be ordinary or quadratic protected parity at sufficiently large height. The comparison between the surviving protected row laws, and partitions with unbounded period or no periodic description, remains open.

