# Exact relative pressure for isolated short phase packets

9 November 2026. A phase-error packet of width \(\ell\le h^{1-\delta}\) has relative cost
\[
 \exp[-c|S|\log^2(h/\ell)]
\]
against the exact protected partition function. The errors inside the packet can be arbitrarily clustered. The proof forces the three black corners of each rooted obstruction far outside the packet, which makes their unthinned conditional overlap sum small.

Fix a protected row/column pair \((c_0,X)\), with selected alphabets of size \(h/2+O(1)\). The row law and its final pair set are fixed. Let \(Z_X(m)\) count the complete normalized-support protected language.

For an interval I of length \(\ell\), and any \(S\subseteq I\), let \(Z_{X,S}(m)\) count valid words with column phase \(X+1_S\). Let \(L=Ch^2\) exceed every forbidden support span.

**Packet theorem.** For every fixed \(\delta>0\), there are \(c>0\) and \(H_\delta\) such that, for \(h\ge H_\delta\), \(1\le\ell\le h^{1-\delta}\), and I at distance at least L from both word ends,
\[
 Z_{X,S}(m)\le Z_X(m)
       \exp[-c|S|\log^2(h/\ell)].
\tag{1}
\]
The constant c can be chosen absolute; the height threshold depends on delta. The theorem is also valid for slightly unbalanced protected references. The complete proof passed [independent review](isolated_packets_independent_audit.md).

## 1. Move all prescribed black cells away from the packet

Put \(\Lambda=1+\log h\), and choose a large absolute A. Set
\[
 B=A\ell\Lambda,\qquad
 R=\left\lfloor\frac{h}{1000B}\right\rfloor.
\tag{2}
\]
For fixed delta and large h, R tends to infinity and
\[
 \log R\ge\tfrac12\log(h/\ell).
\tag{3}
\]

For every completion column \(j\in S\), choose a row w with \(c_0(w)=X(j)\), and put \(W=(j,w)\). Choose a vertical sign \(\epsilon\) toward the farther row boundary. For every primitive \(1\le a,b\le R\), take
\[
 U=(4ka,4\epsilon kb),\qquad
 V=(-4tb,4\epsilon ta),
\tag{4}
\]
with
\[
 \frac{h}{100b}\le k\le\frac{h}{50b},\qquad
 \frac{h}{100a}\le t\le\frac{h}{50a}.
\tag{5}
\]
The rectangle fits vertically. All coordinate increments are divisible by four, so its corners obey the same protected row/column law.

The horizontal side lengths are at least \(h/(25R)\ge40B\). Discard the scale pairs with
\[
 |4ka-4tb|\le4B.
\tag{6}
\]
For fixed a,b,k, this removes at most \(C(B/b+1)\) values of t. Relative to its \(\Theta(h/a)\) choices, the loss is
\[
 O(Ba/(hb)+a/h)\le O(BR/h+R/h).
\]
The numerical constant 1000 in (2) may be enlarged once, so this is a fixed small fraction uniformly over directions. Integer-rounding errors vanish because \(h/R\to\infty\).

The three black corners \(W+U,W+V,W+U+V\) are now at distance at least B from I. They are in distinct columns, and their columns differ from j. Their rows and phases therefore remain the old protected ones, while W has the wrong class at the flipped column j. Each three-point support gives a singleton-axis rival in the new phase model.

The primitive harmonic sum gives \(\Theta(h^2\log^2R)\) retained shapes per completion row. There are \(\Theta(h)\) eligible rows. Three right-triangle corners determine their unique completion, so multiplicity is bounded. Thus every root column has mean at least
\[
 c_1\log^2R.
\tag{7}
\]
All geometries have polynomial horizontal span at most L and fit within the assumed endpoint collars.

## 2. Sum the one-cell incidence over an interval

Use the refined completion-column estimate from
[polynomially spaced parity defects](polynomially_spaced_parity_defects.md).
For a fixed black point P and a completion column at distance \(d>0\), the number of eligible tilted rectangles, summed over its completion rows, is at most
\[
 C h^2\frac{\tau(d)}d+
 C_\eta h^\eta\min(h,h^2/d).
\tag{8}
\]
After prescribing P, the remaining two row choices have probability \(O(h^{-2})\). The resulting conditional mass is bounded by
\[
 C\frac{\tau(d)}d+\frac{C_\eta h^\eta}{\max(h,d)}.
\tag{9}
\]
The raw event incidence at a free column satisfies the same bound, by summing P over its h possible rows and using event probability \(O(h^{-3})\).

Every P used in our family has distance at least B from I. Its distances to the columns of I form an interval \([D,D+\ell-1]\), with \(D\ge B\). The divisor hyperbola gives
\[
 \sum_{D\le n<D+\ell}\tau(n)
 \le C\ell\log(2(D+\ell))+C\sqrt{D+\ell}.
\]
Since \(D\ge B\ge\ell\) and \(D\le L\),
\[
 \sum_{j\in I}\frac{\tau(|P_x-j|)}{|P_x-j|}
 \le C\frac{\ell\Lambda}{B}+\frac C{\sqrt B}
 \le \frac CA+o(1).
\tag{10}
\]
Choose \(0<\eta<\delta\). The diagonal contribution in (9), summed over I, is at most
\[
 C_\eta\ell h^{-1+\eta}=o(1).
\tag{11}
\]
Thus both raw incidence and one-fixed-cell conditional extension mass are at most \(C/A+o(1)\), uniformly over S and its internal pattern.

## 3. Two-cell extensions and the conditional estimate

Two prescribed black cells in distinct columns and one completion column allow only constantly many tilted completions. The completion locus is a circle or a perpendicular line. A vertical perpendicular line would require a horizontal black side, giving an axis rectangle, which is excluded. A horizontal black diagonal uses the circle case and still has at most two intersections with a prescribed column.

Therefore two fixed assignments belong to \(O(\ell)\) rooted events. Their conditional probability mass is
\[
 O(\ell/h)=o(1).
\tag{12}
\]
Three prescribed right-triangle corners determine a unique completion. Deduplicate identical events; distinct rooted events cannot share all three assignments.

Retain the old protected bulk family \(B_0\) whose required black columns avoid S. These events have the same joint product law before and after changing the phase. They remain forbidden regardless of the colors of their shared corners.

The old protected bulk has vanishing raw and conditional extension pressure. In particular, its compatible extensions through the three prescribed cells of a rooted event are \(O_\eta(h^{-1+\eta})\), by the four/six support-extension bounds. This includes three-cell overlaps.

Choose A large enough, then h large enough. Equations (10)--(12) give the joint local-lemma criterion for \(B_0\) and the unthinned rooted family. The exact conditional lower-probability lemma gives
\[
 \Pr(E\mid\text{avoid any earlier listed events})\ge\Pr(E)/2
\tag{13}
\]
for every root event. Avoid \(B_0\) first and then list the roots. Equations (3), (7), and (13) give the extra avoidance factor
\[
 \exp[-c_2|S|\log^2(h/\ell)].
\tag{14}
\]

## 4. Restore the exact old bulk

The old protected events removed from \(B_0\) have total weight at most
\[
 C|S|\Lambda^4/h.
\tag{15}
\]
The conditional local-lemma product bound therefore restores them at cost at most \(\exp(C|S|\Lambda^4/h)\). If the selected class size changes at a flipped column, the product-space ratio is at most \(\exp(C|S|/h)\), since both sizes are \(h/2+O(1)\).

Combining these comparisons,
\[
 \frac{Z_{X,S}(m)}{Z_X(m)}
 \le
 \exp\left[-c_2|S|\log^2(h/\ell)
       +C|S|\Lambda^4/h\right].
\tag{16}
\]
The positive term is absorbed for \(\ell\le h^{1-\delta}\), because
\(\log(h/\ell)\ge\delta\log h\). This proves (1).

This is an exact comparison with the old protected partition function. There is no additive bulk-pressure approximation or interface factor.

## 5. Several isolated packets

Suppose intervals \(I_i\) have lengths \(\ell_i\le h^{1-\delta}\), mutual distance at least \(3L\), and lie away from the word ends. Set \(S_i\subseteq I_i\). The rooted-event neighborhoods from different packets are disjoint. The same joint local-lemma proof gives
\[
 Z_{X,\bigcup_iS_i}(m)\le Z_X(m)
 \exp\left[-c\sum_i|S_i|\log^2(h/\ell_i)\right].
\tag{17}
\]
The old bulk can still connect different neighborhoods; its existing raw and conditional bounds already cover those events.

For a fixed interval of length ell, summing the weights of its nonempty error subsets gives
\[
 a_\ell=
 \left(1+e^{-c\log^2(h/\ell)}\right)^\ell-1.
\]
Uniformly for \(\ell\le h^{1-\delta}\),
\[
 \sum_{\ell\le h^{1-\delta}}a_\ell
 \le \exp[-c_\delta\log^2h]
\]
for large h. Overcount packet collections by allowing a packet of any length to start at every column, without separation restrictions. Their total weighted exponential rate is at most
\[
 1+\exp[-c_\delta\log^2h].
\]
Consequently the union over separated short packets has entropy at most
\[
 \rho_X(h)\left(1+\exp[-c_\delta\log^2h]\right).
\tag{18}
\]
Packets near the two finite ends can be omitted at a fixed-height cost.

The theorem does not control interacting packets at smaller separations, or packets of width comparable to h. Those remain the obstacles to a full phase-domain expansion.

