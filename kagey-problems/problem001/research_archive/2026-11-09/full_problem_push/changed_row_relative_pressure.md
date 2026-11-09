# Exact pressure cost of changing rows in a protected partition

9 November 2026. This note compares a protected phase with the same column phase after changing a small set of row colors. The comparison is against the exact protected partition function. All ten sections have passed [independent review](changed_row_pressure_independent_audit.md).

Let \((c_0,t)\) be a protected row/column pair at a height where the row partition is balanced. Thus
\[
 c_0(y)=\kappa q(y)+\alpha y+\beta,\qquad
 t(x)=\kappa q(x)+\gamma x+\delta,
\]
with \(\alpha=1\) when \(\kappa=0\). Let c be another row coloring with exactly the same two class sizes, and put
\[
 E=\{y:c(y)\ne c_0(y)\},\qquad r=|E|.
\]
The column phase t is kept fixed.

Let \(Z_0(m)\) count protected sea words of length m for \((c_0,t)\), and let \(Z_c(m)\) count valid sea words for the changed row partition c and the same phase t. Both use the complete normalized-support convention and the fixed final axis-pair set of their own partition.

**Theorem.** Fix \(0<d<1\). For every sufficiently large h, uniformly over
\[
 1\le r\le h^{1-d},
\]
there are constants \(C_h<\infty\) and an absolute \(c_*>0\) such that
\[
 Z_c(m)\le C_h Z_0(m)
       \exp\left[-c_*\,\frac{r(\log h)^2}{h}\,m\right].
\tag{1}
\]
The prefactor may depend on h but not on m. In particular the fixed-phase growth rates satisfy
\[
 \rho_{c,t}(h)\le \rho_{c_0,t}(h)
       \exp\left[-c_*\,\frac{r(\log h)^2}{h}\right]
 <\rho_{c_0,t}(h).
\tag{2}
\]

This does not compare the full sea shifts of the two row partitions: changing the row law may make a different column phase favorable. The result fixes the phase t on both sides.

## 1. A uniform two-row rectangle count

We need the following elementary count in the infinite strip, normalized by a specified corner's column.

For fixed rows p,q, the number of tilted rectangles with a specified corner at \((0,p)\) and another corner somewhere in row q is
\[
 O_\epsilon(h^{1+\epsilon})
\tag{3}
\]
uniformly in p,q.

Use the primitive parametrization
\[
 k(a,b),\qquad l(-b,a),\qquad (a,b)=1,\quad a,b,k,l\ge1.
\]
If the two corners are adjacent, their nonzero vertical difference is \(kb\) or \(la\). Factor this difference in at most \(h^{o(1)}\) ways, and count the other vertical product by
\[
 \sum_{a\le h}\lfloor h/a\rfloor=O(h\log h).
\]
A horizontal side would give an axis-aligned rectangle and is excluded from the tilted family.

If the two corners are opposite, their vertical difference has the form \(kb+la\) or \(kb-la\), up to sign. Choose the two positive vertical products in \(O(h)\) ways and factor each in \(h^{o(1)}\) ways. This also covers p=q in the difference case. There are only constantly many corner roles and orientations, proving (3).

If two black points in distinct columns are fixed, the completion corner of their three-black rectangle lies on one of constantly many perpendicular lines or Thales circles. Each such locus meets any prescribed row in \(O(1)\) points. The perpendicular lines are not horizontal: their vertical direction component is the nonzero horizontal difference of the two fixed black points. Thus restricting the completion row to E gives only
\[
 O(r)
\tag{4}
\]
possible rectangles.

## 2. Three-black events created by the changed rows

At a column j, call a changed row y eligible when \(c_0(y)=t(j)\). A protected rectangle whose missing corner is \((j,y)\) then has its completion row excluded from the new column alphabet, while its three other corners remain allowed if their rows avoid E.

Take all such tilted rectangles with four distinct corner columns, and prescribe their three noncompletion black points. These are genuine singleton-axis-rival events for the changed partition. The black row in the completion column belongs to the t(j) class, while y belongs to the other class, so the fixed final axis-pair set supplies the rival.

Each three-point support determines its right triangle and completion uniquely; deduplicate the family if necessary. For finite words retain roots at distance at least the support memory L from both ends.

For every eligible corner W, the number of protected rectangles through W with four distinct columns is
\[
 \Theta(h^2\log^2h),
\tag{5}
\]
uniformly in its row and allowed phase. Only the lower bound is needed. It can be obtained without its precise leading coefficient: choose the primitive directions in a large positive range and take both side scales divisible by four. Every corner then has the same coordinates modulo four as W, so it remains in the protected pattern. Take W as the lowest corner when its row is in the lower half, and as the highest otherwise. The primitive harmonic sum supplies the two logarithms. Repeated-column rectangles are lower order. The full fixed-corner count is recorded in [six_support_leading_pressure.md](six_support_leading_pressure.md).

By (3), excluding rectangles with any other corner row in E loses at most
\[
 O_\epsilon(rh^{1+\epsilon})
\tag{6}
\]
rectangles per W. For \(r\le h^{1-d}\), take \(\epsilon<d\); this is negligible compared with (5).

If t is nonconstant, each changed row is eligible in a fixed positive fraction of the columns of its period, which is at most four. If t is constant, equality of the old and new class sizes means exactly half the changed rows were removed from its selected class. Hence the total eligible-root count, averaged over a period, is at least a fixed positive multiple of r.

Every event has probability \(\Theta(h^{-3})\) under independent uniform choices from the new column alphabets. The rooted event family R therefore has total mean
\[
 \sum_{A\in R}\Pr(A)
 \ge c\,\frac{r(\log h)^2}{h}\,(m-O_h(1)).
\tag{7}
\]
Its total incident probability at any column is
\[
 O\!\left(\frac{r(\log h)^2}{h}\right)=o(1).
\tag{8}
\]
Indeed the normalized geometric count per root column is \(O(rh^2\log^2h)\), each event has three free columns, and the fixed phase period is bounded.

## 3. Retain the common protected bulk

Let B be a complete geometric certificate family of the protected four- and six-cell forbidden supports. Let \(B_0\) retain certificates whose entire geometric row set avoids E. In particular their required black rows are allowed under both row partitions, and all partition-dependent row comparisons in the certificate are unchanged.

The column alphabet sizes are exactly equal before and after the row changes. In each phase class, choose a bijection from the old alphabet to the new one that fixes every unchanged row and matches the removed rows with the inserted rows. The coordinatewise product bijection preserves all events in \(B_0\), so their entire joint distribution, and not only their individual probabilities, is the same in the two models. Every valid changed-partition word avoids both \(B_0\) and R.

The standard protected bulk counts give incident probability
\[
 O_\epsilon(h^{-1+\epsilon})
\tag{9}
\]
per column. Their versions with any one certificate row fixed are
\[
 O_\epsilon(h^{2+\epsilon})\quad\text{for four supports},\qquad
 O_\epsilon(h^{4+\epsilon})\quad\text{for six supports}.
\tag{10}
\]
These bounds remove the free absolute vertical translation from the usual counts. For six supports, one may place the common completion corner at row zero and count two rectangles through it; this gives \(O(h^4\log^4h)\) relative shapes. Fixing any other certificate row chooses at most one vertical translate. The analogous mixed-four count has \(O_\epsilon(h^{2+\epsilon})\) relative shapes. Hidden and horizontal cases obey the same bound.

Consequently the omitted protected bulk has total probability
\[
 \sum_{A\in B\setminus B_0}\Pr(A)
 \le C_\epsilon r m h^{-2+\epsilon}+O_h(1).
\tag{11}
\]

## 4. The unthinned conditional local lemma applies

Use the shared-variable graph for \(B_0\cup R\), and set \(x_A=2\Pr(A)\). Equations (8)--(9) show that the total incident weight tends to zero, uniformly in the changed rows, when \(r\le h^{1-d}\). Each event uses at most six columns. Hence the ordinary local-lemma criterion holds for large h.

Fix a rooted event A and condition on its three row assignments. Compatible rooted events sharing one prescribed black point have, by (3), at most
\[
 O_\epsilon(rh^{1+\epsilon})
\]
possible completions, each with remaining probability \(O(h^{-2})\). Those sharing two prescribed points have only \(O(r)\) possibilities by (4), each with remaining probability \(O(h^{-1})\). A distinct event cannot share all three assignments, by deduplication. Incompatible assignments have conditional probability zero.

Thus the total compatible rooted-neighbor conditional probability is
\[
 O_\epsilon(rh^{-1+\epsilon})+O(r/h)=o(1),
\tag{12}
\]
after taking \(\epsilon<d\). The protected bulk extensions through one, two, or three specified black points contribute only \(O_\epsilon(h^{-1+\epsilon})\), by the established support-overlap bounds.

The arbitrary-event conditional local-lemma inequality and its lower-probability consequence are proved in [relative_sparse_defect_pressure.md](relative_sparse_defect_pressure.md), Section 1. Here the neighboring conditional sums tend to zero without any Bernoulli thinning. Therefore, uniformly over every previously avoided subfamily,
\[
 \Pr(A\mid\text{avoid that subfamily})\ge\Pr(A)/2
\tag{13}
\]
for every rooted event A, once h is large.

Avoid all retained bulk events first, then the rooted events one at a time. Equations (7) and (13) give
\[
 \Pr(\text{avoid }R\mid\text{avoid }B_0)
 \le C_h\exp\left[-c\,\frac{r(\log h)^2}{h}\,m\right].
\tag{14}
\]

## 5. Restore the old bulk and compare exact counts

Use the original protected product space. The full old bulk B satisfies the local lemma. Its conditional product bound and (11) imply
\[
 \Pr(\text{avoid }B\mid\text{avoid }B_0)
 \ge C_h^{-1}
       \exp[-C_\epsilon r m h^{-2+\epsilon}].
\tag{15}
\]
The retained-bulk probability is identical in the old and new product spaces, and the total numbers of product assignments are identical because every column alphabet has the same size.

Multiply (14) by the retained-bulk probability and the common product-space size. Then apply (15) and identify the exact old partition function \(Z_0(m)\). The positive restoration term \(C_\epsilon r h^{-2+\epsilon}\) per column is negligible compared with \(r(\log h)^2/h\). Absorb it into half the negative term to obtain (1), and take exponential growth rates to obtain (2).

The normalized-support convention is used on both sides. The proof does not silently replace a normalized finite-word count by an end-aware finite-board count; changing that convention requires the corresponding common boundary factor.

## 6. Allow a sparse set of column-phase changes as well

Let \(g_h=h^{o(1)}\) be the spacing from
[the exact sparse-defect comparison](relative_sparse_defect_pressure.md).
For a set S of columns whose mutual distances are at least \(g_h\), let
\(Z_{c,S}(m)\) count valid words for the changed row partition c with phase
\[
 t_S(x)=t(x)+1_S(x).
\]
Under the same hypotheses \(1\le r\le h^{1-d}\), there are absolute positive constants \(c_1,c_2\) such that
\[
 Z_{c,S}(m)\le C_h Z_0(m)
 \exp\left[
  -c_1\frac{r(\log h)^2}{h}m
  -c_2|S|(\log h)^2\right].
\tag{16}
\]
This extension has passed independent review.

Retain the old bulk certificates whose geometric rows avoid E and whose required black columns avoid S. Their joint law is unchanged outside S by the classwise alphabet bijections from Section 3. The row variables in S do not occur in these retained events.

Use two rooted families:

- The changed-row events from Section 2, with completion column outside S and all black columns outside S. Their completion row lies in E, while all other geometric rows avoid E.
- The spatial-defect events whose completion column belongs to S, whose four original corners belong to the protected pattern, and whose entire geometric row set avoids E. Their black columns also avoid S.

The first family is unthinned. Mark each event of the second family independently at a sufficiently small fixed rate \(\theta>0\), as in the sparse-defect proof. Both are necessary exclusions for the changed model: in the first family the completion changes row class, and in the second its column phase is flipped while its row class is unchanged.

The separated-root upper bounds are geometric and remain valid for every protected pair: restricting the allowed rows only decreases their counts, and all column alphabets have size \(h/2+O(1)\). The needed positive root degree for each pair follows from the divisible-by-four construction in Section 2. Thus the same spacing and absolute thinning constants may be used for constant, checkerboard, and quadratic protected phases.

Removing row-rooted events that meet S loses at most
\[
 C|S|\,r(\log h)^2/h
\tag{17}
\]
mean, by their incident bound (8), including the excluded completion columns. The spatial-rooted family retains mean at least \(c(\log h)^2\) per interior defect. Excluding completion rows in E loses \(O(r\log^2h/h)\) per defect; excluding black rows in E loses \(O_\epsilon(rh^{-1+\epsilon})\), by (3) summed over the completion row. Both are negligible. The loss from other defect columns is already controlled by the spacing estimate.

The combined incident weight is
\[
 O(\theta)+O(r\log^2h/h)+O_\epsilon(h^{-1+\epsilon}).
\]
For a conditioned changed-row event, compatible marked spatial events sharing one or two assignments have conditional total \(O(\theta)\), by the established separated-root bounds. For a conditioned spatial event, compatible changed-row events have total \(O_\epsilon(rh^{-1+\epsilon})\), by (3)--(4). The within-family bounds are the same as before. No distinct events from these families share all three assignments: their three-point support determines a unique completion column, while the two families place that column outside and inside S respectively.

Thus the conditional lower-probability argument (13) applies to both rooted families, with the same factor one half, after fixing \(\theta\) and taking h large. Their combined mean is bounded below by
\[
 c\frac{r(\log h)^2}{h}m
 +c\theta|S|(\log h)^2
 -C|S|\frac{r(\log h)^2}{h}
 -O_h(1).
\]
Because \(r/h\to0\), the negative term is absorbed into half of the spatial penalty.

Restoring the omitted old bulk costs at most
\[
 C_\epsilon r m h^{-2+\epsilon}
 +C_\epsilon|S|h^{-1+\epsilon}+O_h(1).
\]
At a flipped column the new alphabet can have the other balanced class size. The ratio of the total new and old product-space sizes is therefore at most
\(\exp(O(|S|/h))\), which is also absorbed by the spatial penalty. This proves (16).

Summing over all separated S, and enlarging the sum to all subsets, gives
\[
 \rho_{\mathrm{row+spatial}}(h)
 \le \rho_{c_0,t}(h)
 \exp\left[-c_1r(\log h)^2/h\right]
 \left(1+e^{-c_2(\log h)^2}\right).
\tag{18}
\]
For every \(r\ge1\), the right side is strictly below
\(\rho_{c_0,t}(h)\) once h is large, since
\[
 e^{-c_2(\log h)^2}=o((\log h)^2/h).
\]
Thus a small row perturbation cannot improve the protected phase's entropy even after allowing all sufficiently separated spatial phase defects. The permitted phase profiles form a positive-entropy combinatorial family; the estimate bounds all valid sea words within it.

The conclusion still does not include dense phase domains or arbitrary clusters. Those require additional control beyond the stated spacing condition.

For an ordinary-parity base partition, take the finite union over its four matched affine phases. The resulting changed-partition language still has entropy below the largest old protected-phase rate, and therefore below the ordinary canonical component by [exact entropy capture](dense_residue_entropy_capture.md). This supplies a partition comparison on the entire stated sparse-phase subclass.

## 7. The weighted local-density class also survives row changes

The separation condition can be replaced by the weighted local-density condition from Section 6 of [relative_sparse_defect_pressure.md](relative_sparse_defect_pressure.md). Define
\[
 K_h(u)=\frac{\tau(u)}u+\frac{T_h}{\max(h,u)}
 \quad(1\le u\le L),\qquad K_h(u)=0\quad(u>L),
\]
and
\[
 \mathcal K_h(S)=1+\sup_x
 \sum_{\substack{j\in S\\j\ne x}}K_h(|j-x|).
\]
There is an absolute \(\kappa>0\) such that, if
\[
 \mathcal K_h(S)\le\kappa\log h,
\tag{19}
\]
then, writing C for the clusters obtained by joining successive defects at distance at most \(2L\) and \(D_C=\mathcal K_h(C)\),
\[
 Z_{c,S}(m)\le C_h Z_0(m)
 \exp\left[
 -c_1\frac{r(\log h)^2}{h}m
 -c_2\sum_C\frac{|C|(\log h)^2}{D_C}\right].
\tag{20}
\]
This extension has passed independent review.

Mark the spatial events rooted in cluster C at rate \(b/D_C\), with b a sufficiently small absolute constant. A fixed black point can meet roots from at most one such cluster: every relevant root lies within distance L of its column, whereas different clusters are separated by more than \(2L\). Hence the conditional sums from a changed-row event to the marked spatial events are \(O(b)\), even if its three black points meet different clusters. The reverse conditional sums remain \(O_\epsilon(rh^{-1+\epsilon})\). All other local-lemma estimates are unchanged.

The loss (17) in the row-root mean is still harmless. The spatial penalty in (20) is at least
\[
 \frac{c_2}{\kappa}|S|\log h,
\]
whereas that loss is \(O(|S|(r/h)\log^2h)=o(|S|\log h)\) for \(r\le h^{1-d}\). The other restoration and product-space terms are smaller still. This proves (20).

The existing cluster-activity sum applies after decreasing \(\kappa\) if necessary. Summing all profiles satisfying (19) yields
\[
 \rho_{\mathrm{row+local}}(h)
 \le \rho_{c_0,t}(h)
 \exp[-c_1r(\log h)^2/h]
 \left(1+e^{-c_3(\log h)^2}\right)
 <\rho_{c_0,t}(h).
\tag{21}
\]
Thus the row-partition comparison also allows arbitrarily long clusters with the stated sparse weighted local density. Dense opposite-phase domains remain outside its scope.

## 8. Allow long domains of different protected phases

The row comparison also permits dense domains of different protected phases, provided the total switching frequency is sufficiently small.

Let \(\mathcal X\) be the four column phases matched to the fixed protected row law \(c_0\), and put
\[
 \rho_{\max}(h)=\max_{X\in\mathcal X}\rho_{c_0,X}(h).
\]
A phase word has J protected domains if it can be partitioned into J consecutive intervals, on each of which it agrees with one member of \(\mathcal X\). The intervals may have arbitrary lengths, and the laws are interpreted in the original global column coordinates.

There is an absolute \(c_4>0\) such that the changed-partition sea language with at most
\[
 \nu_hm+O_h(1)\quad\text{domains},\qquad
 \nu_h=\frac{c_4r}{L((\log h)^2+r)},
\tag{22}
\]
has entropy strictly below \(\rho_{\max}(h)\), for \(1\le r\le h^{1-d}\) and sufficiently large h.

### 8.1 Uniform finite-word boundary costs

For each protected phase X, the total probability of its complete four/six bulk family per normalized column is
\[
 O((\log h)^4/h).
\]
This uses the proved mixed-four upper bound and the six-support count. Every support has span at most L. Therefore all events crossing one concatenation cut have total probability at most
\[
 B_h=C L(\log h)^4/h.
\tag{23}
\]
The protected local-lemma criterion holds with twice the event probabilities, so its conditional product bound shows that restoring these crossing events costs at most \(\exp(B_h)\).

If n is a multiple of the phase period, concatenate k admissible n-blocks in the protected product space and restore all crossing events. This gives
\[
 Z_X(kn)\ge e^{-(k-1)B_h}Z_X(n)^k.
\]
Taking exponential growth rates yields
\[
 Z_X(n)\le e^{B_h}\rho_X(h)^n.
\]
For a general n, append at most three letters to reach a phase-period multiple. Conditional LLL gives at least the product of the appended alphabet sizes times \(\exp(-O((\log h)^4/h))\) valid extensions per old word on average. Since
\(\rho_X\le\lceil h/2\rceil\) and every alphabet has size at least \(\lfloor h/2\rfloor\), this padding changes the bound by only an absolute factor. Hence, uniformly in n and in the starting phase,
\[
 Z_X(n)\le
 \exp[C L(\log h)^4/h+O(1)]\,\rho_X(h)^n.
\tag{24}
\]

The endpoint factor in (1) can also be made explicit. Omitting the at most \(2L\) completion columns near the ends loses at most \(C rL(\log h)^2/h\) rooted mean. The omitted-bulk restoration has no additional extensive endpoint cost. Thus the proof of (1), combined with (24), gives
\[
 Z_{c,X}(n)\le
 \exp[B_h(r)]\,\rho_X(h)^n
 \exp[-a_h n],
\tag{25}
\]
where
\[
 a_h=c\,r(\log h)^2/h,\qquad
 B_h(r)\le
 C\frac Lh\bigl((\log h)^4+r(\log h)^2\bigr).
\tag{26}
\]
Enlarging C absorbs bounded phase and short-word effects. These estimates hold for every n, including \(n<2L\).

### 8.2 Count domains and their locations

For a fixed decomposition into J intervals, ignoring compatibility between intervals only enlarges the count. Equation (25) gives
\[
 \#\text{valid words for this decomposition}
 \le \rho_{\max}(h)^m e^{-a_hm+JB_h(r)}.
\]
There are at most \(4^J\binom{m-1}{J-1}\) choices of the phase laws and cuts. Summing over \(J\le\nu m+O_h(1)\), with fixed \(0<\nu<1/2\), bounds the entropy by
\[
 \rho_{\max}(h)
 \exp[-a_h+\nu B_h(r)+H_2(\nu)+\nu\log4].
\tag{27}
\]

Take \(\nu=\nu_h\) from (22). Equations (26) imply
\[
 \nu_hB_h(r)\le Cc_4r(\log h)^2/h.
\]
Also \(\log(1/\nu_h)=O(\log h)\) uniformly for \(1\le r\le h^{1-d}\), since L is polynomial in h. Thus \(H_2(\nu_h)+\nu_h\log4=o(a_h)\). Choose \(c_4\) sufficiently small, then h sufficiently large. The exponent in (27) is at most \(-a_h/2<0\), proving the claim.

This class includes a dense opposite-phase interval of any length, or many such intervals at the permitted switching frequency. It is different from the local-density defect class in Section 7, which controls the positions of individual phase errors. Neither class is asserted to contain every possible competing phase profile.


## 9. Remove the equality-of-class-sizes restriction

Let c be any balanced coloring with \(r\le h^{1-d}\) changed rows. At odd height its labeled class sizes may differ by one from those of \(c_0\). The same fixed-phase comparison remains strict. The logarithmic penalty in (1) still holds except in one case: a constant phase selects the smaller ordinary-parity class, and the only row change enlarges that class. In that case,
\[
 Z_c(m)\le C_h Z_0(m)
       \exp[-c\,m\log h/h].
\tag{28}
\]
This extension removes the class-size restriction for the fixed-phase comparison. Sections 6--8 retain their stated class-size-preserving hypotheses.

### 9.1 Compare retained-bulk counts with one extra letter

Retain \(B_0\) as before. Its events use only unchanged row letters. All changed letters in a given column are therefore interchangeable for this event family. Match the old and new unchanged letters exactly, and regard their changed letters as distinct dummy symbols.

At each column the two dummy multiplicities differ by at most one. Start with the larger alphabet and delete one dummy letter where needed. Under the product distribution, the conditional local-lemma inequality gives
\[
 \Pr(X_j=\text{the deleted letter}\mid\text{avoid }B_0)
 \le \frac2{\lfloor h/2\rfloor}.
\tag{29}
\]
This also holds after earlier deletions: all alphabet sizes remain \(h/2+O(1)\), and the incident bulk weights are still \(o(1)\). Deleting at most one letter per column changes the retained-bulk count by a factor between \(\exp(-Cm/h)\) and 1. Compare both models with their common smaller dummy alphabets to obtain
\[
 e^{-Cm/h}Z_{B_0,\mathrm{old}}(m)
 \le Z_{B_0,\mathrm{new}}(m)
 \le e^{Cm/h}Z_{B_0,\mathrm{old}}(m).
\tag{30}
\]
These are count inequalities, so no further product-alphabet factor is required.

For a nonconstant protected phase, every changed row remains eligible in a positive fraction of columns. For a constant phase, let a and b count the removed and inserted selected-class rows. Balance gives \(|a-b|\le1\) and \(a+b=r\). Unless \(r=1,a=0\), one has \(a\ge r/3\). Thus the old rooted-mean argument still proves (1), with a smaller absolute constant. The extra \(O(1/h)\) pressure in (30) is absorbed by \(cr\log^2h/h\).

### 9.2 The one-row growing-class exception

A constant protected phase belongs to the ordinary-parity family. Its smaller class at odd height is the set of even rows. Thus the exception has odd h, the old alphabet
\[
 A_0=\{2,4,\ldots,h-1\},
\]
and the new alphabet \(A_0\cup\{r_0\}\), where \(r_0\) is odd. The changed final axis-pair set makes \(r_0\) opposite to every other odd row.

Choose the direction from \(r_0\) toward the farther horizontal boundary of the strip. Write its sign as \(\sigma\in\{-1,1\}\), and choose
\[
 1\le d\le H:=\left\lfloor
 \frac{\max(r_0-1,h-r_0)}2\right\rfloor,\qquad d\text{ odd}.
\]
For an integer Pythagorean triple
\[
 u^2+v^2=d^2,\qquad u>0,\quad v\ge0,\quad v\text{ even},
\]
the points
\[
 (x-u,r_0+\sigma d-v),\qquad
 (x+u,r_0+\sigma d+v)
\tag{31}
\]
are both in even rows. Their complementary rectangle corners are
\[
 (x,r_0),\qquad (x,r_0+2\sigma d).
\]
All four points lie between those two white-row levels and hence inside the strip. The two complementary rows have different new row colors. Prescribing the two points in (31) therefore creates an axis rival. If the middle column selects \(r_0\), the tilted presentation becomes a singleton, and the same final axis-pair edge supplies its rival. Otherwise both complementary corners are white. The geometry stays valid when \(v=0\).

There are \(\Theta(h\log h)\) distinct such two-point supports per horizontal translation, uniformly in \(r_0\). For the lower bound use
\[
 u=\ell(a^2-b^2),\qquad v=2\ell ab,\qquad
 d=\ell(a^2+b^2),
\]
where \(a>b\ge1\), \((a,b)=1\), \(a+b\) is odd, and \(\ell\) is odd. Each dyadic range \(a\asymp R,\ b\asymp R\) contains a positive constant times \(R^2\) primitive opposite-parity pairs. It permits a positive constant times \(H/R^2\) odd scales when \(R^2\le H/100\). The \(\Theta(\log h)\) ranges each contribute \(\Omega(H)\) supports. Uniqueness is the usual primitive Pythagorean parametrization. The matching upper bound follows by summing \(O(H/(a^2+b^2))\) over \(a>b\), without the coprimality restriction.

Under the new alphabet, these events have probability \(\Theta(h^{-2})\). Their total mean and incident probability are therefore
\[
 \sum_V\Pr(V)\ge c(m-O_h(1))\log h/h,\qquad
 \sup_j\sum_{V\ni j}\Pr(V)=O(\log h/h).
\tag{32}
\]

Their conditional overlaps are small. If one black point \((x,a)\) is fixed, a second black point \((x',b)\) in an event with white root row \(r_0\) satisfies
\[
 (x'-x)^2=4(a-r_0)(b-r_0).
\tag{33}
\]
Here \(a-r_0\ne0\), since a is even. The squarefree kernel of \(a-r_0\) determines the square class of \(b-r_0\). There are only \(O(\sqrt h)\) possible b, and at most two corresponding horizontal differences. Consequently the compatible one-point overlap sum is \(O(h^{-1/2})\). Two prescribed black points determine the event, so no distinct two-point overlap remains. The conditional protected-bulk extensions contribute \(O_\epsilon(h^{-1+\epsilon})\).

The combined family \(B_0\cup V\) thus satisfies the unthinned local lemma and the same lower conditional-probability estimate used in Section 4. Avoiding V after \(B_0\) costs
\[
 \exp[-c(m-O_h(1))\log h/h].
\]
Restore the omitted old bulk and apply (30). The costs \(O(h^{-2+\epsilon})\) and \(O(1/h)\) per column are both smaller than \(\log h/h\). This proves (28).

The exception cannot be handled by simply treating the inserted row as a black root in the three-point family. Conditioning that black variable leaves total event mass \(\Theta(\log^2h)\), the clique obstruction described in [sparse_defect_unthinned_lll_obstruction.md](sparse_defect_unthinned_lll_obstruction.md). The two-point vertical-rival family supplies the additional pressure instead.


## 10. Arbitrarily clustered errors around one protected phase

The comparison does not need a spacing assumption if the phase-error density is paid for explicitly. Retain the original class-size-preserving hypotheses of Sections 1--8. Let S be any set of phase-error columns, with no restriction on its clusters, and put \(t_S=t+1_S\).

There are absolute constants \(a,C,\sigma_0>0\) such that
\[
 |S|\le\sigma_0m
 \quad\Longrightarrow\quad
 Z_{c,S}(m)\le C_h Z_0(m)
 \exp\left[-a\frac{r\log^2h}{h}m
             +C\frac{\log^4h}{h}|S|\right].
\tag{34}
\]
This extension has passed independent review. In particular, when \(r\gg\log^2h\), every fixed profile with \(|S|=o(m)\) has a strict pressure loss. A union over many profiles requires the additional entropy term described below.

### 10.1 Keep only the changed-row roots

Retain old bulk certificates whose entire row geometry avoids E and whose required black columns avoid S. Retain changed-row rooted events only when their completion column and all three black columns avoid S. No spatial-root event is needed.

The normalized changed-row mean is at least
\[
 c r m\log^2h/h-O_h(1).
\]
At a specified column, the total probability of roots using that column as either a black point or the completion is at most
\[
 C r\log^2h/h.
\]
This follows from the fixed-corner rectangle count and the bounded phase period, and it is uniform in the changed-row set. Deleting every root meeting S therefore loses at most
\[
 C |S|r\log^2h/h.
\tag{35}
\]
Choose \(\sigma_0\) small enough that at least half the original root mean remains.

The retained bulk and roots use only columns outside S. Their product law is the same as in the protected model after the classwise alphabet bijection. The unthinned local-lemma and conditional-root bounds from Section 4 still apply.

The full protected four/six family has total probability \(O(\log^4h/h)\) incident to each column. This is the sharp logarithmic support bound, not the coarser \(h^{-1+\epsilon}\) estimate. Restoring old certificates deleted because of S thus costs at most
\[
 \exp[C|S|\log^4h/h].
\tag{36}
\]
Restoring certificates deleted because of E costs
\[
 \exp[C_\epsilon r m h^{-2+\epsilon}],
\]
as before. The latter cost is absorbed by the changed-row pressure. At odd height, switching the class in columns S changes the product-space size by at most \(\exp(O(|S|/h))\), which is also absorbed by (36).

Avoiding the retained roots, restoring the old bulk, and comparing counts proves (34).

### 10.2 Count all error locations

Let \(Z_{c,\le\sigma}(m)\) count words whose phase differs from the fixed law t in at most \(\sigma m+O_h(1)\) columns. For \(0<\sigma\le\sigma_0\), summing (34) over all error sets gives
\[
 \rho_{c,\le\sigma}(h)
 \le\rho_{c_0,t}(h)
 \exp\left[
 -a\frac{r\log^2h}{h}
 +C\sigma\frac{\log^4h}{h}
 +H_2(\sigma)\right].
\tag{37}
\]
Thus the exact sufficient condition is
\[
 C\sigma\frac{\log^4h}{h}+H_2(\sigma)
 <a\frac{r\log^2h}{h}.
\tag{38}
\]

A convenient uniform choice is
\[
 \sigma\le b\,\frac{r\log h}{h},
\tag{39}
\]
where b is a sufficiently small absolute constant and \(1\le r\le h^{1-d}\). For fixed d and sufficiently large h, \(\sigma\to0\),
\[
 H_2(\sigma)\le 2b\,r\log^2h/h,
\]
and the middle term in (37) is \(o(r\log^2h/h)\). Hence
\[
 \rho_{c,\le\sigma}(h)
 \le\rho_{c_0,t}(h)
       \exp[-a' r\log^2h/h]
 <\rho_{c_0,t}(h).
\tag{40}
\]

A finite union over the four protected base laws replaces the right side by their maximum growth rate. This includes errors concentrated in one long opposite-phase domain, or in arbitrarily many dense clusters, provided their total density obeys (39). It does not require the local-density hypothesis of Section 7.

The result still compares profiles close to one global protected phase. It does not cover a word that spends positive fractions of its length in several different protected domains.






