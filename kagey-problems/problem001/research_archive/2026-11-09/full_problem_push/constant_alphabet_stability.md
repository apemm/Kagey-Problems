# Constant alphabets above density one third force a parity row block

9 November 2026. This is a stability result for one constant column alphabet. It allows the alphabet to omit rows from its partition block, unlike the exact residue-class classification. The geometry, Kneser argument, constants, and primary theorem input passed independent review. The varying-column problem remains open.

**Theorem.** Let \(h\ge3\), let B be one block of a balanced partition of \([1,h]\), and let
\[
 A\subseteq B,\qquad |A|>\lceil h/3\rceil.
\]
Suppose the full shift \(A^{\mathbb Z}\) admits no singleton-axis rival relative to the complete cross-block pair set \(B\times B^c\). Then there is one ordinary parity class P in \([1,h]\) such that
\[
 A\subseteq P\subseteq B,\qquad |B\setminus P|\le1.
\tag{1}
\]
For even h, this forces B to be exactly an ordinary parity class. The possible extra row at odd height is real: one may take A to be the smaller parity class and B to add one row of the other parity.

The threshold is sharp. A largest full residue class modulo three has size \(\lceil h/3\rceil\), is singleton-axis-rival-free inside any block containing it, and can be enlarged to a balanced nonparity block for arbitrarily large h. In particular, the theorem applies to \(|A|\ge0.49h\) for every \(h\ge100\). For integer \(k=|A|\), the threshold is equivalently \(3k>h+2\).

## 1. Two endpoint-completion sumsets lie in B

Write \(u=\min A\), \(v=\max A\), \(\ell=v-u\), and \(k=|A|\). The singleton exclusion implies
\[
 (A+A-u)\cap[1,h]\subseteq B,\qquad
 (A+A-v)\cap[1,h]\subseteq B.
\tag{2}
\]
For example, take black row b=u and the other two black rows a,c in A. If either equals u, the completion \(a+c-u\) is already in A. Otherwise both vertical side differences have the same sign. Choose horizontal side differences 1 and \(-(a-u)(c-u)\); they are nonzero and distinct. The resulting right triangle has three distinct black columns and completion row \(a+c-u\). Its missing corner may share the central column in the unit-diamond case, which is allowed. If the completion row were outside B, it would have a singleton axis rival. This proves the first inclusion; the argument for b=v is identical.

Reduce \(A-u\) modulo \(\ell\), and call the resulting subset of \(\mathbb Z_\ell\) C. Since only its two endpoints merge, \(|C|=k-1\), and \(0\in C\). Every residue in \(C+C\) has its representative in \(B\cap[u,v-1]\): for a nonzero residue, subtract either zero or \(\ell\) from its integer sum and use (2); for residue zero use u, which is already in A. Since v is an additional point of B,
\[
 |C+C|\le|B|-1.
\tag{3}
\]

## 2. Kneser's theorem confines A to one large coset

Let H be the stabilizer of \(C+C\) in \(\mathbb Z_\ell\), and put \(s=|C+H|/|H|\). Kneser's theorem gives
\[
 |B|-1\ge|C+C|\ge(2s-1)|H|,
 \qquad k-1=|C|\le s|H|.
\]
We use the standard finite-abelian-group statement, as proved in [Matt DeVos, *A short proof of Kneser's addition theorem for abelian groups*](https://arxiv.org/abs/1303.3539).

If \(s\ge2\), these inequalities give
\[
 3(k-1)\le2(|B|-1),
 \qquad 3k\le2|B|+1\le h+2,
\tag{4}
\]
contrary to the hypothesis. Hence \(s=1\). Since \(0\in C\), we have \(C\subseteq H\), and its nonempty H-periodic sumset is \(C+C=H\). If its index were at least three, then
\[
 \ell\ge3|H|\ge3(k-1),\qquad 3k\le\ell+3\le h+2,
\]
again a contradiction. Thus H has index one or two.

Suppose H has index one. Then \(C+C=\mathbb Z_\ell\), so (2) fills the whole interval \([u,v]\) with rows of B. In particular \(\ell\le|B|-1\le(h-1)/2\). Put \(L_0=u-1\), \(R_0=h-v\), and \(S=A+A-2u\subseteq[0,2\ell]\). The interval already filled has \(\ell+1\) rows.

Every sum \(z\in S\) with \(z<\ell\) gives the lower outside completion \(u+z-\ell\); every sum with \(z>\ell\) gives the upper outside completion \(u+z\). These completions are distinct and outside \([u,v]\). At most
\[
 (\ell-L_0)_++(\ell-R_0)_+\le\ell
\]
of them lie outside the board, because \(L_0+R_0=h-\ell-1\ge\ell\). Thus (2), together with the filled interval, gives
\[
 |B|\ge(\ell+1)+(|S|-1-\ell)
       =|S|=|A+A|\ge2k-1.
\]
The last bound exceeds \((h+1)/2\) under the hypothesis on k, contradicting balance.

Therefore H has index two. The index-two subgroup of \(\mathbb Z_\ell\) consists of the even residues. Since \(C\subseteq H\), all rows of A have one physical parity, proving \(A\subseteq P\).

## 3. A sumset pigeonhole argument fills the whole parity class

Identify P with \([1,n]\), where \(2n\le h+1\), and use the same letters for the rescaled row sets. If \(r\in P\setminus B\), then \(A+A\) and \(r+A\) must be disjoint. Indeed an intersection would give \(a+c-b=r\), with a,b,c in A. Neither \(a=b\) nor \(c=b\) can hold, because either would put r in A. Their physical row differences are nonzero and even. Horizontal side differences 1 and minus their product give a tilted rectangle with four distinct columns. Its missing row r would have a singleton axis rival, contrary to the hypothesis.

But both sumsets lie in \([2,2n]\), while
\[
 |A+A|+|r+A|\ge(2k-1)+k=3k-1>2n-1.
\tag{5}
\]
They cannot be disjoint. Therefore \(P\subseteq B\).

Finally \(|B|\le\lceil h/2\rceil\) and \(|P|\ge\lfloor h/2\rfloor\), giving \(|B\setminus P|\le1\). This completes (1).

This is a genuine near-half stability statement, but only for a column-independent alphabet A. It does not assert that general high-entropy containers contain such a constant alphabet, or that their varying row sets must follow one protected phase.

## 4. Vertical rivals remove the odd-height exception

If the constant box also admits no vertical-pair axis rival, then B is exactly an ordinary parity class at every height.

The only remaining case to exclude has \(h=2n+1\),
\[
 P=\{2,4,\ldots,2n\},\qquad B=P\cup\{s\}
\]
for one odd row s. For every odd row r in the opposite residue class modulo four from s, the midpoint \(a=(r+s)/2\) is an even row in P. If \(a\in A\), the two black points
\[
 (-d,a),(d,a),\qquad d=|r-s|/2,
\]
form a tilted rectangle with the vertical white pair \((0,r),(0,s)\). Since \(s\in B\), \(r\in B^c\), and the selected row at column zero is even, this pair has the axis rival from \(B\times B^c\). Therefore each such midpoint is excluded from A.

There are at least \(\lfloor(n+1)/2\rfloor\) distinct excluded midpoints, so
\[
 |A|\le n-\lfloor(n+1)/2\rfloor
       =\lfloor n/2\rfloor
       <\lceil h/3\rceil.
\]
This contradicts the theorem's hypothesis. The corollary uses only singleton and vertical-pair rivals; it does not assert that the remaining four- and six-cell supports vanish.
