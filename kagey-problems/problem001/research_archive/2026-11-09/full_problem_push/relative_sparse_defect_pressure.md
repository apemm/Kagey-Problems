# Exact relative pressure for sufficiently separated parity defects

9 November 2026. A conditional local-lemma argument compares sparse-defect words directly with the exact protected partition function. It removes the extensive error in the earlier absolute Suen estimates. The complete argument, including the local-density extension, passed [independent review](protected_phase_pressure_independent_audit.md).

Let \(L=2W_h=O(h^2)\), and use the normalized support-language convention throughout this note. Let \(Z_{\mathrm O}(m)\) be the exact number of length-m all-odd protected words avoiding its complete minimal four/six support family. Let \(N_S(m)\) count valid ordinary-parity sea words with even-row letters exactly in a prescribed set S of columns and odd-row letters elsewhere.

Use the spacing from [polynomially_spaced_parity_defects.md](polynomially_spaced_parity_defects.md):
\[
 T_h=\max_{1\le n\le\lceil4(L+h^2)^2\rceil}\tau(n),\qquad
 g_h=\lceil T_h(1+\log h)^2\rceil=h^{o(1)}.
\]
If the distinct members of S are at distance at least \(g_h\), then for all sufficiently large h,
\[
 N_S(m)\le C_h Z_{\mathrm O}(m)
                \exp[-c|S|\log^2h],
\tag{1}
\]
where \(c>0\) is absolute and \(C_h\) does not depend on m or S.

Consequently the full \(g_h\)-separated-defect sublanguage has entropy
\[
 r_g(h)\le r_{\mathrm O}(h)
       \bigl(1+\exp[-c\log^2h]\bigr).
\tag{2}
\]
There is no \(O(h^{-2+\varepsilon})\) term in this comparison.

The normalized language can reject geometrically valid finite prefixes because a witness's common white cells can lie outside the prefix. Equation (1) uses one convention on both sides. The proof also applies directly to a consistently chosen end-aware event family and its own protected partition function; it does not identify those two different finite-word counts.

## 1. Two conditional local-lemma facts

Consider events \(E_i\) in a product probability space. Connect two events when their variable sets overlap. Suppose numbers \(0<x_i<1\) satisfy
\[
 p_i:=\Pr(E_i)\le x_i\prod_{j\in\Gamma(i)}(1-x_j).
\tag{3}
\]
The fundamental conditional local-lemma bound gives
\(\Pr(E_i\mid\bigcap_{j\in S}\overline E_j)\le x_i\)
for any \(S\) not containing i. In particular, sequential avoidance gives the corresponding product lower bound. The standard statement and proof are given in [Moser--Tardos, Theorem 1.1](https://arxiv.org/html/0903.0544v3).

For any other event A, including an event not in this family,
\[
 \Pr\left(A\mid\bigcap_{j\in S}\overline E_j\right)
 \le \Pr(A)
       \prod_{\substack{j\in S\\V(E_j)\cap V(A)\ne\varnothing}}
                   (1-x_j)^{-1}.
\tag{4}
\]
To prove this, split S into events whose variable sets meet A and those disjoint from it. A is independent of the entire disjoint subfamily. Bound the numerator by ignoring the neighboring events, and bound their conditional avoidance probability in the denominator by the local-lemma product.

We will use (4) to get a lower conditional probability for one assignment event \(E_i\). Split an arbitrary avoided subset S into its neighbors N of \(E_i\) and its nonneighbors D. Since \(E_i\) is a fixed assignment of some variables, conditioning on it leaves a product distribution on the other variables; every event in D keeps exactly its original law and local-lemma bounds.

If
\[
 \sum_{j\in N}\Pr(E_j\mid E_i)\le b_i
\]
and all the inverse products in (4), applied to residual \(E_j\) in that conditioned product space, are at most two, then
\[
 \Pr(E_i\mid\text{avoid }S)\ge p_i(1-2b_i).
\tag{5}
\]
Indeed (4) and a union bound give
\[
 \Pr(\text{avoid }N\mid E_i,\text{avoid }D)\ge1-2b_i.
\]
Bayes' formula expresses the left side of (5) as \(p_i\) times this quantity divided by \(\Pr(\text{avoid }N\mid\text{avoid }D)\le1\).

## 2. The bulk and rooted families

Fix the profile S. Let B be all ordinary protected minimal four/six events, and let \(B_0\subseteq B\) be those whose black support avoids S. Their distribution under the mixed profile is identical to their distribution under the all-odd product measure.

For each defect column j at distance at least L from the word's ends, take the three-cell events from all all-odd tilted rectangles with four distinct corner columns and completion in column j. Require their three black columns to avoid S. These are genuine singleton-axis-rival events under this profile. Deduplicate them: the same three prescribed black points determine their rectangle and completion uniquely.

Let R be this rooted family. The incidence and overlap estimates in the subpolynomial-spacing note give:

- Each root retains mean at least \(c_0\log^2h\).
- The sum of rooted probabilities incident with any free column is bounded by an absolute constant.
- Through a fixed black point, there are \(O(h^2)\) rooted events.
- Through two fixed black points in different columns, there are \(O(h)\) rooted events in total, across all root columns.

The last statement uses the perpendicular-line/Thales-circle completion locus; the fixed columns differ, so no horizontal line with unbounded strip intersection occurs.

Independently mark each rooted event with probability \(\theta>0\), and retain its indicator only when its marker is one. Write \(R^\theta\) for these assignment events, now fixing three row variables and their own Bernoulli marker. Keep the bulk events unmarked.

Choose \(\theta\) as a sufficiently small absolute constant. The shared-variable graph for \(B_0\cup R^\theta\) then has incident probability sum
\[
 O(\theta)+O_\varepsilon(h^{-1+\varepsilon})
\]
at any row variable, while each marker belongs to one event only. Thus \(x_i=2p_i\) satisfies (3): the sum of neighboring x-values is less than \(1/2\), so their product is at least \(1/2\). The same observation bounds every inverse product needed in (4) by two.

## 3. Every rooted event keeps a fixed fraction of its probability

Fix \(E_i\in R^\theta\). Conditional on its three row assignments, compatible other rooted events sharing one black assignment have total conditional probability \(O(\theta)\): there are \(O(h^2)\) choices and each has remaining probability \(O(\theta h^{-2})\).

Those sharing two black assignments also contribute \(O(\theta)\), since there are \(O(h)\) choices with remaining probability \(O(\theta h^{-1})\). A distinct event cannot share all three assignments, by deduplication. Incompatible assignments have conditional probability zero.

The neighboring bulk events contribute only
\[
 O_\varepsilon(h^{-1+\varepsilon})
\]
conditionally. For a size-s bulk support sharing r of the three fixed assignments, the established extension bound gives \(O_\varepsilon(h^{s-r-1+\varepsilon})\) choices and remaining probability \(O(h^{-(s-r)})\), for \(s=4,6\), \(1\le r\le3\). No bulk support is contained in the three assignments.

Therefore
\[
 \sum_{j\in\Gamma(i)}\Pr(E_j\mid E_i)
 \le C\theta+O_\varepsilon(h^{-1+\varepsilon}).
\tag{6}
\]
Take \(\theta\) small enough, then h large enough, to make this at most \(1/4\). Equation (5) yields the uniform bound
\[
 \Pr(E_i\mid\text{avoid }S')\ge p_i/2
\tag{7}
\]
for every subset \(S'\subseteq B_0\cup R^\theta\) not containing i.

In particular, condition first on avoiding all retained bulk events, then avoid the rooted marked events one by one. Equation (7) gives
\[
 \Pr(\text{avoid }R^\theta\mid\text{avoid }B_0)
 \le \exp\left(-\frac12\sum_{i\in R^\theta}p_i\right)
 \le C_h\exp[-c_1|S|\log^2h].
\tag{8}
\]
The at most \(2L\) omitted end roots contribute only \(C_h\). Avoiding the original rooted events implies avoiding the marked ones, so (8) is an upper bound for valid words.

## 4. Restore the omitted bulk without an extensive error

Now use the all-odd product measure. The total probability of the omitted bulk events \(B\setminus B_0\) is at most
\[
 O_\varepsilon(|S|h^{-1+\varepsilon}),
\]
because each such event touches a defect column. The ordinary bulk family alone satisfies (3). Its conditional product lower bound gives
\[
 \Pr(\text{avoid }B\mid\text{avoid }B_0)
 \ge \exp[-C_\varepsilon|S|h^{-1+\varepsilon}].
\tag{9}
\]
Thus the retained-bulk partition function differs from the exact protected one by at most this factor, depending on the number of defects and not on m separately.

Put \(k=\lceil h/2\rceil\). The mixed profile's product-space size is
\[
 k^{m-|S|}\lfloor h/2\rfloor^{|S|}\le k^m.
\]
Multiply (8) by the retained-bulk probability, use (9), and identify \(k^m\Pr(\text{avoid }B)=Z_{\mathrm O}(m)\). The positive error \(C_\varepsilon|S|h^{-1+\varepsilon}\) is absorbed by the negative root penalty. This proves (1).

Finally, summing (1) over all separated profiles and then enlarging the sum to all subsets gives
\[
 \sum_S N_S(m)
 \le C_h Z_{\mathrm O}(m)
        \bigl(1+e^{-c\log^2h}\bigr)^m,
\]
which proves (2).

## 5. A quantitative consequence with a defect-frequency hypothesis

If a family of such separated profiles has at least \(\delta m-O_h(1)\) defects per length-m word, then its entropy is at most
\[
 r_{\mathrm O}(h)
 \exp\!\left[\sup_{p\ge\delta}
       \{H_2(p)-cp\log^2h\}\right],
\tag{10}
\]
where \(H_2(p)=-p\log p-(1-p)\log(1-p)\). In particular it is strictly below \(r_{\mathrm O}(h)\) whenever the displayed supremum is negative, for example when \(\delta\) is inverse-polynomial in h with a fixed exponent.

This does not establish such a frequency bound for arbitrary noncanonical components. Exact entropy capture of a positive fraction of protected cores does not imply that every protected core is in the canonical component. The conditional frequency premise is therefore stated explicitly rather than inferred from the capture theorem.

## 6. Exact comparison under a weighted local-density condition

The same argument allows arbitrarily long defect clusters. Define
\[
 K_h(d)=\frac{\tau(d)}d+\frac{T_h}{\max(h,d)}
 \quad(1\le d\le L)
\]
and set \(K_h(d)=0\) outside this range. For a set S of defect columns, put
\[
 \mathcal K_h(S)=1+\sup_{x\in\mathbb Z}
       \sum_{\substack{j\in S\\j\ne x}}K_h(|j-x|).
\tag{11}
\]
There are absolute \(\kappa,c>0\) such that the entropy
\(r_{\mathrm{loc}}(h)\) of the valid parity language satisfying
\(\mathcal K_h(S)\le\kappa\log h\) obeys
\[
 r_{\mathrm{loc}}(h)
 \le r_{\mathrm O}(h)\bigl(1+e^{-c\log^2h}\bigr).
\tag{12}
\]
This includes all sufficiently large h with the spacing condition in (1), but it does not require a bound on cluster size or total defect count.

Join consecutive defects whose gap is at most \(2L\), and write C for the resulting clusters. Put \(D_C=\mathcal K_h(C)\). Rooted families belonging to distinct clusters use disjoint row variables. The refined incidence estimates give, for each C:

- The rooted probability incident with any row variable is at most \(C_0D_C\).
- At most \(C_0h^2D_C\) rooted events contain one specified black point.
- At most \(C_0h\) contain two specified black points in distinct columns, regardless of the number of roots.
- Removing events whose black columns meet S loses at most \(C_0D_C\) mean per root.

Here and below \(C_0\) denotes an absolute constant, unrelated to a defect cluster. The last estimate applies the same incidence kernel at the completion column. No other cluster can cause a loss, because its roots are farther than \(2L\).

Since \(D_C\le\kappa\log h=o(\log^2h)\), each cluster retains mean at least \(c_0|C|\log^2h\). Mark its rooted events at rate
\[
 \theta_C=b/D_C
\]
for a sufficiently small absolute b. The shared-variable incident mass is now \(O(b)+O_\varepsilon(h^{-1+\varepsilon})\), uniformly over all clusters. In the conditional estimate (6), the one-shared-assignment contribution is \(O(\theta_CD_C)=O(b)\), and the two-shared-assignment contribution is \(O(\theta_C)\le O(b)\). Bulk extensions remain \(O_\varepsilon(h^{-1+\varepsilon})\). Thus (7) holds with the same absolute factor one half.

Avoid the rooted events sequentially after all retained bulk events. Restore the omitted bulk as in Section 4. Since its cost per defect is \(O_\varepsilon(h^{-1+\varepsilon})\), it is absorbed by the cluster penalty. This proves the exact profile estimate
\[
 N_S(m)\le C_h Z_{\mathrm O}(m)
 \exp\left[-c_1\sum_C
       \frac{|C|\log^2h}{D_C}\right].
\tag{13}
\]
Omitting at most \(2L\) end roots changes only \(C_h\), even when one cluster has arbitrarily many defects.

It remains to sum these profiles. For a q-point cluster,
\[
 D_C\le C_2\left[
  1+\log^2(q+1)+qT_h/h\right],
\tag{14}
\]
by the divisor rearrangement estimate in
[clustered_parity_defects.md](clustered_parity_defects.md).
For \(q<\log h\), the last term is o(1). The activity of all such clusters is therefore at most \(e^{-c_2\log^2h}\), by the small-cluster calculation in that note.

For \(q\ge\log h\), instead use \(D_C\le\kappa\log h\). After specifying the first defect, there are at most \((2L)^{q-1}\) successive gap choices. Choose \(\kappa\) so small that \(c_1/\kappa>10\). Since \(\log(2L)\le3\log h\) for large h, the q-cluster activity is at most
\[
 \exp[-7q\log h].
\]
Its sum over all \(q\ge\log h\) is \(e^{-\Omega(\log^2h)}\). Allowing independent cluster candidates at an arbitrary subset of starting columns overcounts the profiles by at most \((1+e^{-c\log^2h})^m\). Combining this with (13) proves (12).

The criterion is local and hereditary under deleting defects. In particular, finite restrictions of an infinite profile satisfying (11) satisfy the same bound. It excludes large weighted local defect density; it makes no assertion about a dense domain of the opposite parity.

