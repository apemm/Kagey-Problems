# Continuation: an exact lower bound on phase-witness frequency

9 November 2026. A nonzero row perturbation cannot compete with the quadratic protected rate merely by using rare transitions between locally protected phases. The exact comparison below forces a quantitative frequency of phase-far blocks or changes of the nearest protected law.

The comparison retains the complete reference bulk. Its boundary factor is explicit, so there is no extensive span-tail error. It does not establish general dominance, because it gives a necessary witness frequency rather than ruling out all such witnesses.

Use the normalized fixed-final-F support language throughout. Let c_0 be a quadratic protected row law, including either translated variant when its class sizes differ by two. Let c be balanced, with
\[
 E=\{y:c(y)\ne c_0(y)\},\qquad
 1\le r=|E|\le\delta_0h,
 \qquad
 P=P_h(r)=\frac rh\log^2\frac hr.
\]
Here delta_0 is a sufficiently small absolute constant. Let
\[
 r_{\rm ref}(h)=\max_{X\in\mathcal X(c_0)}r_{c_0,X}(h),
 \qquad \Lambda=1+\log h.
\]

Partition the columns into aligned h-column blocks. Fix the small absolute local cap epsilon_0 from [the exact local-cap theorem](continuation_exact_row_local_cap.md). A block is good if its actual phase differs from a matched quadratic law on at most epsilon_0 h columns. Otherwise it is bad. The matched law of a good block is unique for large h.

A witness is either a bad block or an edge joining two adjacent good blocks with different matched laws. Let K(w) be the total number of witnesses in the word, ignoring the final incomplete block.

**Theorem.** There are absolute positive constants a,c and a height threshold such that the language with
\[
 K(w)\le \nu_h m+O_h(1),\qquad
 \nu_h=c\,\frac{P_h(r)}{h\Lambda^2}
      =c\,\frac{r\log^2(h/r)}{h^2\Lambda^2}
\tag{1}
\]
has exponential growth at most
\[
 r_{\rm ref}(h)\exp[-aP_h(r)].
\tag{2}
\]
Consequently it has strictly smaller growth than the balanced quadratic protected sea for large h, including r=1.

In the range \(r\le h^{1-d}\), (1) permits
\[
 \nu_h=c_d\,r/h^2.
\tag{3}
\]
In particular, throughout the already proved \(O((1+\log\log h)^2)\) optimizer neighborhood, a competing nonquadratic component must have at least order \(r/h^2\) witnesses per column.

The last assertion is a necessary entropy condition. It is not a claim that every word in a competing component has that frequency.

## 1. The finite-interval exact comparison

Consider one interval of n=Mh columns, with \(M\ge D_0\), throughout which all blocks are good with the same globally indexed law X. Let q_i be their error counts.

The joint root proof gives
\[
 \sum_{\substack{S:\ |S\cap I_i|\le\epsilon_0h}}
 Z_{c,S}(n)
 \le
 Z_{0,X}(n)
 \exp[-aP n+C h+C\sqrt{rh}
               +(n/h)e^{-b\log^2h}],
\tag{4}
\]
uniformly in the starting phase. The constant D_0 is fixed and sufficiently large. The count on the left only imposes the necessary constraints whose supports lie in the interval; this suffices when restricting a globally valid sea word.

Here are the finite-end details behind (4).

For row roots, use the adaptive primitive family with
\(R=\lfloor\sqrt{h/r}\rfloor\). Its period-averaged mean is at least aP per column. Its full span-weighted endpoint loss is \(C rR\le C\sqrt{rh}\), by [adaptive row pressure](adaptive_row_root_pressure.md). Retain only roots whose completion and black columns avoid S. Translation invariance bounds the lost mean by CP|S|.

For phase roots, use the one-sided geometry
\[
 U=(4ka,4kb),\qquad V=(4lb,-4la),
\tag{5}
\]
with the completion row in the central third of the strip. Choose the direction with at least n/2 available columns. For a root in block i, put
\[
 Q_i=\max_j\min\!\left(q_j,h\left(\frac K{1+|i-j|}\right)^4\right),
 \qquad
 R_i=\left\lfloor
       \min\{c(h/Q_i)^{1/4},\,M/C_1\}
      \right\rfloor.
\tag{6}
\]
The maximum ranges only over this interval. With C_1 large, every black support stays in the interval, including for roots adjacent to either end. Discard ka=lb and every black column in S. Delete all geometric rows in E.

The capped maximal inequality from [the one-sided proof](full_protected_row_leading_pressure.md) gives phase-root mean
\[
 b\sum_iq_i
       \min\{\log^2(h/q_i),\log^2M\}.
\tag{7}
\]
The row-root and phase-root families have no distinct shared-three event: three black corners determine a unique completion, which belongs to E for the first family and to its complement for the second. Their raw and compatible conditional masses are small after choosing epsilon_0 and delta_0. Therefore the same unthinned conditional local-lemma comparison applies jointly.

Retain old canonical bulk whose entire geometry avoids E and whose required black columns avoid S. Common white corners may lie outside the interval; the normalized support convention still forbids their black support in every globally valid word. Restore the complete reference bulk using its conditional product bound. Its cost is
\[
 C_\eta rn h^{-2+\eta}
       +C|S|\Lambda^4/h+Cn/h.
\]
The last term is the exact dummy-letter comparison when alphabet sizes differ by O(1). These terms and CP|S| are absorbed by the row penalty and (7). Choose D_0 so that the minimum capped phase penalty is a sufficiently large positive constant per error.

Summing error descriptions uses
\[
 \begin{split}
 &\log\!\left[
 1+\sum_{1\le q\le\epsilon_0h}
  \binom hq
  e^{-bq\min\{\log^2(h/q),\log^2M\}}
 \right]\\
 &\hspace{20mm}\le
 e^{-b'\log^2h}+Ch e^{-b'\log^2M}.
 \end{split}
\tag{8}
\]
Over M blocks, the second term costs
\(ChM e^{-b'\log^2M}\le C'h\), because its supremum over \(M\ge D_0\) is finite. This proves (4).

The exact protected cut bound is
\[
 Z_{0,X}(n)\le e^{Ch\Lambda^2}\,r_{c_0,X}^{\,n},
\tag{9}
\]
uniformly in n and the starting phase. Its proof retains all crossing events and bounds their total probability weight by \(Ch\Lambda^2\); see [the span-weighted interface note](protected_crossing_bulk_weight.md).

Since \(\sqrt{rh}\le h\), equations (4)--(9) imply
\[
 \sum_S Z_{c,S}(n)
 \le
 r_{\rm ref}^{\,n}
 \exp[-aP n+Ch\Lambda^2].
\tag{10}
\]
The negligible \(n h^{-1}e^{-b\log^2h}\) term is absorbed into P, uniformly down to r=1. This is an exact-reference estimate, not a leading-pressure truncation.

## 2. Decompose a word using all its witnesses

For a fixed witness description, place every bad block and every transition pair into a guard. Expand each guard by D_0 blocks and merge across gaps shorter than D_0. Absorb short end intervals.

The final guard has at most
\[
 C D_0hK+O_h(1)
\tag{11}
\]
columns. Every complementary interval contains at least D_0 blocks, is good throughout, and has one matched law. There are at most K+1 such intervals.

Count each guard column by h, ignoring every constraint there. This loses only
\[
 \exp[O(hK)+O_h(1)]
\]
relative to \(r_{\rm ref}\), since \(h/r_{\rm ref}\) is bounded for large h. Omitting the row penalty from these columns costs at most
\(CP hK\), also absorbed by \(Ch\Lambda^2K\).

Apply (10) separately to each complementary interval. Ignoring cross-interval constraints enlarges the count. For a fixed witness description and interval labels, the resulting bound is
\[
 C_h r_{\rm ref}^{\,m}
 \exp[-aP m+Ch\Lambda^2K].
\tag{12}
\]
The factor C_h includes the two finite ends and is independent of m.

There are at most
\[
 \binom{2\lceil m/h\rceil}{K}C^K
\tag{13}
\]
possible witness-start/type descriptions. The at most K+1 interval labels add only another constant to the factor C^K. Guard words are already counted directly, so they need no separate phase-profile factor.

## 3. Sum descriptions at low witness density

Suppose \(K/m\le\nu_h+o(1)\). Choose c in (1) small enough that
\[
 Ch\Lambda^2\nu_h\le aP/4.
\]
The logarithm of (13), divided by m, is at most
\[
 \frac2h H_2(h\nu_h/2)+\nu_h\log C
 \le C'\nu_h\log\frac{e}{h\nu_h}.
\tag{14}
\]
This is \(o(P)\), uniformly for \(1\le r\le\delta_0h\). Indeed
\[
 \frac{\nu_h}{P}=\frac{c}{h\Lambda^2},
\]
and \(\log(e/(h\nu_h))=O(\Lambda)\) throughout the range. Summing all K below the cutoff therefore proves (2).

The exact quadratic-variant comparison gives
\[
 |\log r_{\rm ref}-\log r_{\rm Q}|\le C/h,
\]
where r_Q is the balanced quadratic protected rate. Since
\[
 \min_{1\le r\le\delta_0h}P_h(r)
   =\log^2h/h
\]
for large h, the negative term in (2) absorbs this variant difference. Thus (2) is strictly below r_Q.

## 4. Consequence for a hypothetical competing component

Let a competing irreducible component have Perron root at least r_Q, and use its Perron measure. Each ergodic piece of the h-step shift has the same entropy per physical column. Apply the word-counting theorem to such a piece. If its witness frequency were less than the threshold in (1), almost all long blocks would lie in a language with entropy strictly below \(\log r_Q\), a contradiction. The same argument applies to any h-step ergodic piece whose own entropy is at least \(\log r_Q\); a general stationary mixture need not give that entropy to every piece.

Equivalently, each such maximum-entropy piece must have positive witness density at least
\[
 c\,\frac{r\log^2(h/r)}{h^2\Lambda^2}.
\tag{15}
\]
For a periodic irreducible finite-state component, this statement applies to every cyclic h-step piece of its Perron measure. It does not assert the bound for arbitrary low-entropy measures supported on the same component.

This narrows the exact comparison problem. A nonquadratic competitor must use enough genuinely nonuniform phase behavior to pay a positive transition frequency. The present upper bound still allows the exact interface factor \(e^{Ch\Lambda^2}\) per witness. Determining its sign relative to the rooted wall deficit, or constructing a finite returning gate in every competitive component, remains open.

The complete comparison passed [independent review](continuation_exact_row_pressure_independent_audit.md).

