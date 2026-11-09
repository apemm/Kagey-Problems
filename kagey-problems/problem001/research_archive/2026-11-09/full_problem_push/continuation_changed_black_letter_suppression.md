# Continuation: arbitrary clusters of changed black letters are rare in a fixed phase

9 November 2026. In one fixed matched quadratic phase, restoring changed black letters has a superpolynomially small effect on the exact partition function. The proof handles arbitrary clusters by deleting overloaded weighted stars. It makes no assertion about arbitrary boundary conditioning or a wall between different phases.

Let \((c_0,X)\) be a quadratic protected row/column pair, including a translated row law with imbalance two. Let c be balanced and differ from c_0 on E, with
\[
 1\le r=|E|\le h^{1/4}.
\tag{1}
\]
Set
\[
 A_x=\{y\notin E:c_0(y)=X(x)\},\qquad
 D_x=\{y\in E:c(y)=X(x)\}.
\tag{2}
\]
The common alphabets A_x have size \(h/2+O(r)\). The letters in D_x have the wrong reference color: \(c_0(y)\ne X(x)\).

Fix an interval I and a set \(J\subseteq I\). Outside J use A_x; inside J also allow D_x. Let \(Z_J(t;I)\) count valid words with weight \(e^t\) for each selected D-letter. Let \(Z_\varnothing(I)\) be the common-alphabet count for the actual final partition c.

All counts use the projected fixed-phase, fixed-final-F support language. The phase X is specified on the whole line. A singleton-rival support whose completion column lies outside I is therefore still forbidden when its three black support cells lie inside I. This is a normalized sea-language convention, not a statement about an isolated finite board with no prescribed exterior phase.

**Theorem.** There are absolute positive c,C such that, for large h, every \(0\le t\le1\), and \(|I|\ge Ch^{9/8}\),
\[
 1\le
 \frac{Z_J(t;I)}{Z_\varnothing(I)}
 \le
 \exp\left[
 C|J|\frac rh\exp\{-c(1+\log h)^{3/2}\}
 \right].
\tag{3}
\]
Constants are independent of I, J, E, r, and t.

The lower bound uses t>=0 and the inclusion of the common alphabet. Shorter intervals can be absorbed into a fixed-height end factor for exponential-growth statements.

The correction in (3) includes every placement and every cluster of changed letters. It does not require a spacing or local-density hypothesis.

## 1. The common-alphabet base has a uniform local lemma

Use the minimal canonical family
\[
 {\cal B}=B^\sharp\cup T^\sharp\cup V
\]
from [the common-alphabet surface comparison](continuation_common_alphabet_surface.md). The universal bulk consists of four/six supports. The extra T supports are singleton-rival triples completed in E. The extra V supports are two-black vertical rivals with exactly one displayed endpoint in E.

Under the independent A_x alphabets, its raw incident and compatible extension sums are
\[
 O_\eta(rh^{-1/2}+h^{-1+\eta})=o(1)
\tag{4}
\]
for a fixed small eta. All containments and identical constraints are removed before using the conditional estimate.

If constraints touching a set S of black columns are omitted, the conditional product bound restores them at cost
\[
 \exp(C\delta_h|S|),\qquad \delta_h=o(1).
\tag{5}
\]
This is uniform in S. No separation of its columns is needed.

For a fixed set of changed letters
\[
 {\cal S}=\{(x,a_x):x\in S,\ a_x\in D_x\},
\]
every remaining base support avoiding S is still forbidden in the actual model. Its law is unchanged on the unforced variables. Consequently, before imposing additional roots, the count for this letter assignment is at most
\[
 Z_\varnothing(I)\prod_{x\in S}|A_x|^{-1}
                  \exp(C\delta_h|S|).
\tag{6}
\]

## 2. A one-sided two-variable family at a changed black cell

Fix a changed black cell \(P=(j,a)\), with \(a\in D_j\). Put
\[
 R=\lfloor h^{1/8}\rfloor.
\]
Choose the vertical sign epsilon toward the farther row boundary. For primitive u,v with
\[
 1\le u,v\le R,\qquad u+v\ \hbox{odd},\qquad u>1000v,
\]
take
\[
 U=(2ku,2\epsilon kv),\qquad
 V=(4lv,-4\epsilon lu),
\tag{7}
\]
where k is odd and
\[
 h/(100v)\le k\le h/(50v),\qquad
 h/(100u)\le l\le h/(50u).
\tag{8}
\]
The white completion and two free black cells are
\[
 W=P-V,\qquad A=P+U-V,\qquad B=P+U.
\tag{9}
\]
The sides U,V are perpendicular.

Both free black columns lie to the right of j, because \(U_x>V_x>0\). Reflect horizontally when the leftward available interval is longer. Their distances from j are at most ChR. Thus every root has both free black cells inside I when \(|I|\ge ChR\), including roots at either finite end. The completion W can lie on the other side of the root. Its phase is still X by the stated projected-language convention.

Every vertical displacement from P in (9) is toward the chosen row boundary and has size less than h/4. Thus the four cells fit in the strip.

Write the adjusted protected color as
\[
 F(x,y)=c_0(y)+X(x)\pmod2.
\]
At P, F=1. Since k is odd and u+v is odd, adding U changes F by one. Adding V changes F by zero, because both its coordinates are divisible by four. Hence
\[
 F(A)=F(B)=0,\qquad F(W)=1.
\]
Delete every geometry whose free or completion row belongs to E. Then A,B belong to the common alphabets, whereas W has actual row color different from X at its column. With P selected, the two free black cells therefore force a singleton axis rival at W.

There are
\[
 \Theta(h^2\log^2R)=\Theta(h^2\log^2h)
\tag{10}
\]
such pairs per P. Restricting u>1000v leaves a fixed positive fraction of the primitive harmonic sum, as does the opposite-parity restriction and odd k. Requiring one of the other three rows to lie in E removes at most
\[
 CrhR\log R=o(h^2\log^2R)
\tag{11}
\]
choices, uniformly in (1).

Also discard directions with \(u^2+v^2\) a square. Their harmonic weight is bounded:
\[
 \sum_{\substack{u>1000v\\u^2+v^2\ {\rm square}}}\frac1{uv}
 \le C\sum_{v\ge1}\frac{\tau(v^2)}{v^2}<\infty.
\tag{12}
\]
Indeed \((s-u)(s+u)=v^2\), and u>1000v. Thus (10) is unchanged.

This last deletion ensures that the free pair A,B, whose difference is V, has noninteger Euclidean length. It cannot itself be a base vertical-rival support. No other base constraint has two or fewer required assignments.

The unmarked root mean is therefore
\[
 c\Lambda^2\le \mu_P\le C\Lambda^2,\qquad
 \Lambda=1+\log h.
\tag{13}
\]

## 3. Three weighted incidence tests

Let \({\cal V}=\{(j,a):j\in J,\ a\in D_j\}\) be the candidate changed letters. Its elements are vertices for the following weighted stars. Constants can normalize every weight to lie in [0,1].

A fixed letter assignment \({\cal S}\subseteq{\cal V}\) uses at most one vertex in each physical column.

### 3.1 Conditional incidence at a free cell

For a free cell C, let \(w_C(P)\) be a constant multiple of
\[
 \sum_{\substack{\text{root pairs at }P\\ C\text{ is a free cell}}}
 \Pr(\text{the other free assignment}).
\tag{14}
\]
One fixed P and C leave O(h) possibilities on a nonhorizontal perpendicular line, or \(h^{o(1)}\) possibilities on a circle. Hence \(w_C(P)\le1\) after normalization.

Let \(T_h=h^{o(1)}\) dominate the required divisor and circle counts up to polynomial size. Then
\[
 \sum_{P\in{\cal V}}w_C(P)
 \le CrT_h(R+\Lambda).
\tag{15}
\]
For the side role \(C=B\), a fixed changed row a fixes \(2kv=C_y-a\). Sum over divisors v and over u<=R; the remaining scale contributes O(1/u) to the conditional weight. This gives \(CT_h\Lambda\) per changed row.

For the diagonal role \(C=A\), there are O(hR) possible root columns per changed row. Each fixed diagonal has at most \(CT_h\) circle choices, contributing \(CT_h/h\). This gives \(CRT_h\) per row. These two estimates prove (15).

### 3.2 Loss from occupied columns

For each candidate root P, let \(w_P^{\rm del}(Q)\) be a constant multiple of the unmarked mean of its pairs having a free cell in the column of Q. The row value specified by Q is irrelevant for this deletion test.

The fixed-column parameter count is at most ChR^2. In the diagonal role it uses the progression
\[
 ku-2lv=d/2,
\]
with at most \(C(h/(uv)+1)\) solutions for each direction. The side role is simpler. Therefore each weight is at most \(CR^2/h<1\).

Summing over all columns counts each pair only twice. There are at most r candidate letters per column, so
\[
 \sum_{Q\in{\cal V}}w_P^{\rm del}(Q)\le Cr\Lambda^2.
\tag{16}
\]

### 3.3 Duplicate free pairs

For each pair of distinct free assignments C,D, give weight one to every candidate root P whose family contains exactly that pair. A fixed free pair determines the side V. Its possible roots lie on a nonhorizontal line perpendicular to V. Each changed row gives O(1) roots, so
\[
 \sum_{P\in{\cal V}}w_{C,D}^{\rm pair}(P)\le Cr.
\tag{17}
\]
This test is necessary. Distinct changed roots can force the same two free assignments; they cannot be silently treated as distinct independent violations.

All weights in (14)--(17) have positive size at least \(h^{-C}\) after normalization, so there are O(Lambda) nonempty dyadic weight bins. Uniformly over all star centers, (15)--(17) are bounded by
\[
 W_h\le h^{3/8+o(1)}\le h^{1/2}
\tag{18}
\]
for large h.

Only polynomially many centers are relevant per candidate column. Free cells lie within ChR of J. Free pairs arise from the O(rh^2 Lambda^2) root shapes per candidate column. Thus the total number of centers is at most
\[
 |J|h^{C_0}
\tag{19}
\]
for an absolute C_0. This estimate remains valid when J is disconnected.

## 4. Delete overloaded stars by a maximal matching

Put
\[
 H=\lceil\sqrt\Lambda\rceil.
\]
For every star center and dyadic bin with weights in
\((2^{-j-1},2^{-j}]\), put
\[
 b_j=\left\lceil \frac{H\,2^j}{(j+1)^2}\right\rceil.
\tag{20}
\]
Create a hyperedge for every b_j-subset of vertices in that bin.

If a vertex set G contains no hyperedge, each of its weighted star sums is at most CH. Indeed each bin has fewer than b_j occupied vertices, and
\[
 \sum_{j\ge0}b_j2^{-j}\le CH.
\tag{21}
\]

Given any actual changed-letter set \({\cal S}\), choose a maximal collection of vertex-disjoint hyperedges contained in it. Let B be their union, and let
\[
 G={\cal S}\setminus B.
\]
Maximality implies that G contains no hyperedge. Thus all three tests for G are bounded by CH.

The set B is not discarded from the actual word. It is discarded only from the root family. Its columns remain occupied and must be removed from every root pair based at G.

For a root in G, deleting the other columns of G loses at most CH mean by the second test. Summed over roots in G, deleting the columns of B loses at most
\[
 CH|B|.
\tag{22}
\]
To prove (22), fix one column of B. The first test bounds the total conditional incidence of G-roots at each allowed free row by CH. Multiply by that row's probability and sum the rows. The raw incident mean in the whole column is at most CH.

Using (13), the total root mean remaining after deleting every column of \({\cal S}\) is at least
\[
 c\Lambda^2|G|-CH|G|-CH|B|.
\tag{23}
\]

## 5. Mark the remaining two-variable events

Give each retained root-pair occurrence its own independent Bernoulli mark of mean b/H, where b is a sufficiently small absolute constant.

The first star test bounds raw incident and compatible one-assignment masses by CH before marking. The third test bounds distinct marked occurrences with the same two assignments by CH. After marking, all these sums are small absolute constants.

Base constraints avoiding S contribute only o(1) compatible extension mass through two prescribed free cells, by (4). An identical base V event is impossible by (12). Constraints of larger arity cause only proper partial-assignment extensions.

Thus the joint marked family and the retained base satisfy the local lemma and its conditional lower-probability estimate. Listing the base first, then the marked roots, gives an avoidance factor at most
\[
 \exp\left[-c\frac{\Lambda^2}{H}|G|+C|B|\right].
\tag{24}
\]
The term CH|G| in (23) is absorbed into its leading term.

A genuinely valid word avoids every unmarked root violation, hence every marked one, for every realization of the marks. Marking therefore supplies a valid counting upper bound.

Combine (6) and (24). For a fixed \({\cal S}\), with its selected disjoint hyperedges, the count is at most
\[
 Z_\varnothing(I)
 \left(\frac Ch\right)^{|B|}
 \left(\frac Ch e^{-c\Lambda^2/H}\right)^{|G|}.
\tag{25}
\]
This bound includes the harmless \(e^{C\delta_h|S|}\) base-restoration factor and \(e^{t|S|}\), uniformly for \(0\le t\le1\).

## 6. The overloaded hyperedges have tiny total activity

Give a hyperedge Q activity \((C/h)^{|Q|}\). In one star bin, its number of vertices satisfies
\[
 n_j\le 2^{j+1}W_h.
\]
Hence the total activity of its b_j-subsets is at most
\[
 \binom{n_j}{b_j}\left(\frac Ch\right)^{b_j}
 \le
 \left(\frac{CW_h(j+1)^2}{hH}\right)^{b_j}.
\tag{26}
\]
By (18), the base is at most \(h^{-1/3}\) for large h. Also \(b_j\ge cH\), and there are O(Lambda) bins. Thus each center contributes at most
\[
 \exp(-cH\Lambda).
\]
After the polynomial center count (19),
\[
 \sum_{\text{all hyperedges }Q}
       (C/h)^{|Q|}
 \le
 C|J|e^{-cH\Lambda}
 \le C|J|e^{-c\Lambda^{3/2}}.
\tag{27}
\]

Now sum (25). Overcount every collection of disjoint selected hyperedges by allowing arbitrary collections. Overcount the remaining good letters by allowing arbitrary subsets of \({\cal V}\). The maximal-matching construction guarantees that every original \({\cal S}\) has at least one counted description. Therefore
\[
 \frac{Z_J(t;I)}{Z_\varnothing(I)}
 \le
 \prod_Q\left(1+(C/h)^{|Q|}\right)
 \prod_{P\in{\cal V}}
    \left(1+\frac Ch e^{-c\Lambda^2/H}\right).
\tag{28}
\]
The first logarithm is bounded by (27). The second is at most
\[
 C|J|\frac rh e^{-c\Lambda^2/H}.
\]
Since \(H\asymp\sqrt\Lambda\) and \(r/h\ge1/h\), decreasing c absorbs the extra factor h in the first term. This proves (3).

The argument does not assume that overloaded stars are rare under the final conditioned measure. It sums their activities explicitly.

## 7. Rarity and pressure consequences

Let \(\zeta_{\rm full}(c;X)\) be the full fixed-phase growth rate and \(\zeta_{\rm common}(c;X)\) the common-alphabet rate. Taking J=I and exponential rates in (3) gives
\[
 0\le
 \log\zeta_{\rm full}(c;X)-\log\zeta_{\rm common}(c;X)
 \le
 C\frac rh e^{-c\Lambda^{3/2}}.
\tag{29}
\]

The same proof is uniform for fugacity t in [0,1]. Convexity of \(\log Z_J(t;I)\) therefore gives
\[
 \mathbb E[\text{number of selected changed letters}]
 \le
 C|J|\frac rh e^{-c\Lambda^{3/2}}
\tag{30}
\]
under the ordinary free finite-volume fixed-phase measure.

For any Perron maximum-entropy measure of the full fixed-phase shift, the variational principle applied to the weighted pressure gives the corresponding frequency bound
\[
 \mu(\text{selected row belongs to }E)
 \le C\frac rh e^{-c\Lambda^{3/2}}.
\tag{31}
\]
For a period-four presentation this means the physical-column average, or equivalently the average over its four phases.

Equations (30)--(31) are averaged rarity statements. They are not bounds under an arbitrary prescribed boundary or after fixing an arbitrary outside configuration.

## 8. Controlled collars preserve the favorable surface sign

Suppose changed letters are restored only in a set J of at most \(h^A\) columns around an interface, for any fixed A. Equation (3) changes each of the union and two half-interval partition functions by \(1+o(1)\), provided both halves have length at least L_h. Thus restoring arbitrary clusters of the *new* changed letters in these collars changes the exact interface logarithm by o(1).

Restoring the old protected letters in the reference collar has a different effect. These are ordinary protected letters, so they are not rare. Nevertheless, their interface effect is \(o(rh)\).

Indeed, under either old alphabet, every crossing protected event has conditional probability \(p(1+O_\eta(h^{-1+\eta}))\). Required black supports using a specified row have total crossing weight \(O(\Lambda^2)\). For a uniform proof, embed the height-h geometry in a height-2h strip and translate vertically by multiples of four. Each fixed-row support gives \(\Theta(h)\) distinct translates preserving its phase and cut. The global \(O(h\Lambda^2)\) crossing bound then gives the asserted fixed-row bound. Restoring r rows therefore adds at most \(Cr\Lambda^2\) crossing mean. On common assignments, alphabet denominators change by relative \(O(r/h)\), also costing at most \(Cr\Lambda^2\) against the total \(Ch\Lambda^2\) cut mean. The conditional errors are \(O_\eta(h^\eta\Lambda^2)=o(rh)\).

Consequently the \(-\Theta(rh)\) result of
[the common-alphabet surface theorem](continuation_common_alphabet_surface.md)
survives arbitrary changed-letter clusters inside polynomial-width collars. In particular, it applies to fully restored same-phase interfaces when both half lengths lie between L_h and a fixed power of h.

This is still a same-phase statement. A genuine wall changes the completion phase of crossing rectangles, so its constraint family is different. Nor does finite-collar restoration establish localization under arbitrary exterior conditioning. Exact component dominance and exact quadratic optimality remain open.

Independent review passed. See [changed_black_letter_suppression_independent_audit.md](changed_black_letter_suppression_independent_audit.md).

