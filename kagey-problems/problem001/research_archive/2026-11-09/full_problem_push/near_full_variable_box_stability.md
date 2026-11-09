# Stability of near-full Cartesian row-class boxes

9 November 2026. This extends the exact full-row-class classification to arbitrary column alphabets that omit at most M rows from their selected balanced block. The row partition need not be known or periodic. The theorem, constants, and finite-boundary argument passed independent review. The finite-width obstruction in Section 6 was added afterward.

Let M be a nonnegative integer, and let \(B_0,B_1\) be a balanced partition of \([1,h]\), with row-color function c. For every column \(x\in[1,m]\), choose a phase \(t_x\in\mathbb F_2\) and a nonempty alphabet
\[
 A_x\subseteq B_{t_x},\qquad |B_{t_x}\setminus A_x|\le M.
\tag{1}
\]
The Cartesian box consists of all sea words choosing one row from each \(A_x\). We assume that every such word avoids singleton-axis and vertical-pair axis rivals relative to the complete cross-block pair set \(B_0\times B_1\). Other forbidden supports are not needed for the conclusion.

**Theorem.** There are absolute constants K,C such that, if
\[
 h\ge C(M+1),\qquad m\ge4h+20,
\tag{2}
\]
then there are \(\kappa,\alpha,\beta,\gamma,\delta\in\mathbb F_2\) for which
\[
 \#\{y\in[1,h]:
 c(y)\ne \kappa q(y)+\alpha y+\beta\}\le KM,
 \qquad q(y)=\binom y2\bmod2,
\tag{3}
\]
and
\[
 t_x=\kappa q(x)+\gamma x+\delta
 \quad\text{for every }x\in[1,m].
\tag{4}
\]
If \(\kappa=0\), then \(\alpha=1\). Thus the row partition is close to ordinary or quadratic parity, and the column phase has the corresponding exact form.

The approximating quadratic row law need not itself be balanced at the same finite height. For example \(q(y)+y\) has a two-row imbalance when \(h\equiv2\pmod4\); a balanced partition may differ from it in one row. The theorem does not discard this possibility.

The same conclusion holds for a bi-infinite Cartesian box. Conversely, (3)--(4) alone do not guarantee validity, even for the two rival types under consideration.

## 1. A vertical-reflection dichotomy

For \(s\in\mathbb F_2\) and \(k\ge1\), put
\[
 n_s(k)=\#\{a\in B_s:a-k,a+k\in[1,h],\
                            c(a-k)\ne c(a+k)\}.
\]
If \(n_s(k)>2M\), then
\[
 t_x=t_{x+2k}=s
\tag{5}
\]
is impossible whenever the two columns are present.

Indeed the two alphabets in (5) omit at most \(2M\) possible center rows. Choose an available a counted by \(n_s(k)\), and put black points at \((x,a)\) and \((x+2k,a)\). The other diagonal is the vertical pair at column \(x+k\), in rows \(a-k,a+k\). Its rows lie in different blocks. Since every alphabet has at least two rows under (2), choose the selected row at the middle column to avoid the one displayed row in its block. Both displayed corners are then white, producing the forbidden axis rival.

If one color s has \(n_s(k)\le2M\) for every k, then
\[
 V(B_s)=\sum_k n_s(k)\le Mh.
\]
The [interval reflection-stability theorem](reflection_interval_stability.md) shows that c differs from an ordinary parity law in at most \(K_0M\) rows, for an absolute \(K_0\). This is already (3) with \(\kappa=0,\alpha=1\).

Otherwise choose \(k_0,k_1\) with \(n_s(k_s)>2M\), and write
\[
 a_0=2k_0,\qquad b_0=2k_1,\qquad p=a_0+b_0\le2h-2.
\]
The constraints are no two zeros at distance \(a_0\) and no two ones at distance \(b_0\). They imply
\[
 t_{x+p}=t_x
 \quad(x+p\le m),
\tag{6}
\]
because a zero forces a one after \(a_0\), which forces a zero after another \(b_0\), and the reverse-color chain uses the steps in the opposite order. They also imply
\[
 t_{x+a_0}=1-t_x
 \quad(x+p\le m).
\tag{7}
\]
For a zero this is immediate. If both \(t_x\) and \(t_{x+a_0}\) were one, the latter would force \(t_{x+p}=0\), contradicting (6).

Thus every geometry placed sufficiently far from the right edge has a horizontally translated context with all four phases complemented.

## 2. Complementary contexts give nearly constant even row differences

For every even \(a\ge2\), consider a tilted rectangle with vertical side increments both equal to a, and horizontal side increments \(a/2\) and \(-2a\). The dot product is zero. After a horizontal translation its four columns are
\[
 0,\ a/2,\ 2a,\ 5a/2,
\]
which are distinct, while its four row values are
\[
 y,\ y+a,\ y+a,\ y+2a.
\]
Take \(2a\le h-1\). Also use \(a=3\), with horizontal side increments 1 and \(-9\), giving four distinct columns in a span of 10. Thus the available row shifts are every multiple of 4, together with 6.

Place each rectangle's leftmost column at 1. Its horizontal span is at most \(\max(5h/4,10)\). Adding \(p\le2h-2\) remains below the width in (2), so (7) holds at all four columns. A second placement at horizontal translate \(a_0\) therefore has the complementary phase vector.

Let \(\sigma_{2a}\) be the XOR of the four phases in the first placement. If
\[
 c(y)+c(y+2a)\ne\sigma_{2a},
\]
the row-color vector and the phase vector agree at either one or three corners. In one of the two complementary placements they agree at exactly three corners. Unless a matching row is omitted from its alphabet, that placement gives three black corners and one opposite-block white corner, hence a singleton-axis rival.

Across both placements there are eight corner-column incidences. At each incidence at most M translated row values are omitted. Therefore
\[
 \#\{y\in[1,h-d]:c(y+d)+c(y)\ne\sigma_d\}\le8M
 \quad\text{for }d\in\{4,8,12,\ldots\}\cup\{6\},\ d<h.
\tag{8}
\]
The cancellation of the two middle row colors is why equal vertical increments are useful here.

## 3. Nearly constant differences force a quadratic row law

Assume \(M\ge1\), and let \(D=8M\). All following inequalities hold once \(h\ge1000(M+1)\).

Compare three successive shifts of length 4 with two successive shifts of length 6. Among the \(h-12\) possible starting rows, at most \(5D\) fail one of the five identities from (8). A good starting row therefore exists, and cancellation gives
\[
 3\sigma_4=2\sigma_6,\qquad\text{hence}\qquad\sigma_4=0.
\tag{9}
\]
Put \(\kappa=\sigma_6\).

Similarly, for d divisible by 4 and \(h-d-4>3D\), choose a row at which the identities for shifts d,4,d+4 all hold. This gives
\[
 \sigma_{d+4}=\sigma_d+\sigma_4=\sigma_d.
\]
Starting with d=4, we obtain
\[
 \sigma_d=0
 \quad\text{for every }4\mid d,\ 4\le d\le h-R,
 \qquad R=32M+16.
\tag{10}
\]

Define \(\eta(y)=c(y)+\kappa q(y)\). For even d,
\[
 q(y+d)+q(y)=d/2\bmod2.
\]
For d divisible by 4, equations (8)--(10) show that \(\eta(y+d)\ne\eta(y)\) at at most D positions. The same holds for d=6. For \(d\equiv2\pmod4\), \(d\ge10\), compose the identities at shifts \(d-6\) and 6; at most \(2D\) starting rows fail either identity. Thus every even \(4\le d\le h-R\) has at most \(2D\) mismatches for \(\eta\).

Count unordered pairs of rows of the same physical parity on which \(\eta\) differs. Distances 2 contribute at most h pairs. The controlled distances contribute at most \(Dh\). Distances greater than \(h-R\) contribute at most \(R^2/2\). Since \(R\le48M\) and \(h\ge1000M\), the total is at most
\[
 h+8Mh+R^2/2\le20Mh.
\tag{11}
\]
For a physical parity class P of size \(N_P\), let \(r_P\le N_P/2\) be the minority count of \(\eta\) on P. That class contributes
\[
 r_P(N_P-r_P)\ge r_P(h-1)/4
\]
to (11). Consequently,
\[
 r_{\mathrm{even}}+r_{\mathrm{odd}}\le100M.
\tag{12}
\]
Choose the majority value of \(\eta\) separately on the two physical parity classes. These two values have the form \(\alpha y+\beta\), proving (3) with K=100 in the heavy/heavy branch.

If \(\kappa=0\) and \(\alpha=0\), this approximating law is constant. Balance would require at least \(\lfloor h/2\rfloor\) errors, contrary to (12) and \(h\ge1000(M+1)\). Thus \(\alpha=1\) in the ordinary case.

For \(M=0\), the [exact full-row-class theorem](full_row_class_phase_classification.md) supplies the conclusion directly. Alternatively the same difference argument can be completed without the deliberately discarded edge distances.

Combining this section with the first branch, take
\[
 K=\max(K_0,100).
\]

## 4. The phase becomes exact on the entire column interval

Let
\[
 c_0(y)=\kappa q(y)+\alpha y+\beta
\]
be the row law from (3). Apply the two small rectangle templates
\[
 T_2:\ (1,2),(2,-1),\qquad
 T_3:\ (1,3),(3,-1)
\]
to any column interval in which they fit. Their column sets are respectively
\[
 \{x,x+1,x+2,x+3\},\qquad
 \{x,x+1,x+3,x+4\}.
\]
Their row-color XORs under \(c_0\) are respectively 0 and \(\kappa\).

Suppose the corresponding phase XOR is wrong. If \(\kappa=0\), shifting all rows by 1 complements their \(c_0\)-colors. If \(\kappa=1\), shifting by 2 complements them. Thus at least \(h/2-4\) vertical translations have exactly three corners whose \(c_0\)-colors match the phases.

At most \(4KM\) of these translations touch a row where c differs from \(c_0\), and at most \(4M\) touch an omitted row at a matching corner. If
\[
 h/2-4>4(K+1)M,
\tag{13}
\]
one surviving translation gives a singleton-axis rival. Therefore both phase XORs are correct everywhere:
\[
 \begin{aligned}
 t_x+t_{x+1}+t_{x+2}+t_{x+3}&=0,\\
 t_x+t_{x+1}+t_{x+3}+t_{x+4}&=\kappa.
 \end{aligned}
\tag{14}
\]
Writing \(d_x=t_x+t_{x+1}\), these become
\[
 d_x=d_{x+2},\qquad d_x+d_{x+3}=\kappa.
\]
On any five-column interval they already force \(d_x=\kappa x+\gamma\), and the same relation propagates across the full word. Integrating gives (4).

Choose the absolute constant C in (2) larger than both 1000 and \(16(K+1)\). Then all estimates used above, including (13), hold. The proof is complete.

## 5. Scope for the counting problem

This theorem concerns a Cartesian box in which **every** choice of a row from each alphabet avoids the specified rivals. It does not assert that every high-entropy component contains such a box, or that an entropy container itself has this property. Therefore it is a structural stability theorem for near-full product alphabets, not a proof of general component dominance.

The result nevertheless removes both restrictions of the earlier period-two and period-four arguments: the row partition is initially arbitrary, and the column alphabets and phase may vary without any prescribed period.

## 6. A fixed column width cannot suffice

For every fixed \(m\ge2\), there are arbitrarily tall near-full boxes satisfying the two rival exclusions whose row partitions stay far from every ordinary or quadratic law. Thus some dependence of the width on height is necessary.

Put \(R=2(m-1)^2+2\), choose \(h=4n\) with \(2n>R+2\), and define
\[
 c(y)=
 \begin{cases}
 y\bmod2,&y\le2n,\\
 y+1\bmod2,&y>2n.
 \end{cases}
\]
Both blocks have size \(2n\). In every one of the m columns use the same alphabet
\[
 A=\{y\le2n-R:y\text{ is even}\}
   \ \cup\
   \{y\ge2n+R+1:y\text{ is odd}\},
\]
with phase zero. Because R is even, exactly R rows of \(B_0\) are omitted.

There is no singleton-axis rival. Three black corners of a tilted rectangle in a sea form a right triangle in three distinct columns. Its two vertical leg differences are nonzero: a zero vertical difference would make the other side vertical and repeat the right-angle column. Their product in absolute value equals the product of the horizontal leg differences, and is therefore at most \((m-1)^2\).

If the three black rows meet both retained regions, at least one vertical leg difference has magnitude at least \(2R+1\), a contradiction. If all three lie in one retained region, a completion beyond the row-color switch would require both leg differences to have magnitude at least R, again a contradiction. Therefore the three black corners and the completion lie in one ordinary-parity region, where the completion has the same color as the three black rows.

There is also no vertical-pair rival. Let two black endpoints have horizontal separation \(1\le D\le m-1\), vertical separation v, and diagonal length \(L=\sqrt{D^2+v^2}\). A vertical diagonal with integral endpoints requires L to be an integer.

If the black rows lie in different retained regions, \(v\ge2R+1\), so
\[
 0<L-v=\frac{D^2}{L+v}<1.
\]
This precludes integral L. If the rows lie in the same retained region, each endpoint of the vertical diagonal extends beyond their row interval by at most
\[
 (L-v)/2\le D/2<R.
\]
Thus both displayed rows stay in the same row-color region whenever they remain on the board. The black rows have the same physical parity, and integrality of the displayed rows forces L even. Their two colors therefore agree, so no cross-block axis pair is exposed.

The row coloring differs from either ordinary parity law in exactly \(h/2\) rows. It differs from each quadratic law in \(h/2+O(1)\) rows, as follows by counting the period-four pattern separately in the two halves. Hence no constant-width version of (3), with an absolute \(O(M)\) bound, is possible as \(h\to\infty\).

This example verifies only the singleton and vertical-rival exclusions used by the theorem. It does not claim that every word of this box is a valid full sea.

