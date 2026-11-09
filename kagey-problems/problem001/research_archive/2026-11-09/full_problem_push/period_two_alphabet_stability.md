# Stability of near-half Cartesian boxes of column period two

9 November 2026. This extends the constant-alphabet theorem to two alternating column alphabets. The proof, including the density constant below, passed independent review. Period-four boxes are treated separately.

Let \(h\ge100\), let \(B_0,B_1\) be a balanced partition of \([1,h]\), and let \(A_0,A_1\) be two row alphabets with
\[
 |A_0|,|A_1|\ge0.45h.
\]
Each \(A_i\) is contained in one of the two row blocks. Consider the Cartesian box allowing \(A_0\) at even columns and \(A_1\) at odd columns. Assume no assignment in this box has a singleton-axis rival relative to the complete cross-block pair set.

Then the following classification holds.

1. If the two alphabets lie in the same row block B, there is a physical parity class P with \(P\subseteq B\), \(|B\setminus P|\le1\), and \(A_i\subseteq P\cup(B\setminus P)\). If vertical-pair axis rivals are also excluded, \(B=P\).
2. If the two alphabets lie in opposite blocks, the partition is exactly ordinary parity. After choosing the parity label, \(A_0\) consists only of rows of one physical parity and \(A_1\) only of the other. Thus the box follows an ordinary checkerboard law.

The proof uses only bounded integer rectangles of horizontal span \(O(h^2)\). The same conclusions hold from the corresponding local exclusion condition on a periodic Cartesian window of width at least \(2h^2+10\), with the fixed complete pair set used for its axis rivals.

## 1. The same-block case

The intersection \(A=A_0\cap A_1\) has size at least
\[
 0.90h-\lceil h/2\rceil\ge0.40h-0.5>\lceil h/3\rceil.
\]
The constant box \(A^{\mathbb Z}\) is contained in the period-two box. Apply [constant_alphabet_stability.md](constant_alphabet_stability.md), including its vertical-rival corollary when appropriate.

## 2. Good rows in the opposite-block case

Relabel so \(A_i\subseteq B_i\), and put \(c(y)=i\) on \(B_i\). Let
\[
 G=A_0\cup A_1,\qquad e=h-|G|\le0.10h.
\]
For every good row \(y\in G\), its allowed column parity is precisely \(c(y)\). Translating the whole Cartesian box by one column gives another singleton-free box, with the complementary column rule.

Consequently, whenever the four good rows
\[
 a,\quad a+d,\quad y,\quad y+d
\]
are in the strip and \(d(y-a)\notin\{0,1,-1\}\), we have
\[
 c(a)+c(a+d)+c(y)+c(y+d)=0.
\tag{1}
\]
Use rectangle sides \((1,d)\) and \((-d(y-a),y-a)\). The four corner columns are distinct under the stated restriction. If the row-color XOR were one, the four cell colors \(c(r)+x\pmod2\) would also have odd XOR, because the sum of the corner columns is even. Exactly three corners would then be allowed in one of the two translated boxes. The missing corner has the opposite row-block color at its column, giving the excluded singleton axis rival.

## 3. A dense partial Freiman relation is affine

Put \(D=\lfloor h/2\rfloor\). For each \(1\le d\le D\), there are at least
\[
 h-d-2e\ge0.30h
\]
good pairs \(x,x+d\in G\). Equation (1) shows that
\[
 f_d=c(x+d)+c(x)
\]
is independent of the chosen good pair. If \(d\ge2\), any two distinct pairs satisfy (1) directly. If \(d=1\), the only exceptional comparison is between adjacent pair starts; a third good pair with start at distance at least two from each bypasses it. There are far more than the four excluded starts.

For \(1\le d<D\), some triple \(x,x+d,x+d+1\) lies in G: the number of possible starts is at least
\[
 h-d-1-3e\ge0.20h.
\]
Comparing its differences gives \(f_{d+1}=f_d+f_1\), so \(f_d=d\gamma\), where \(\gamma=f_1\).

Choose good anchors
\[
 u\in[\lceil h/3\rceil,D],\qquad
 v\in[h-D,\lfloor2h/3\rfloor].
\]
Each interval has more than e positions when \(h\ge100\). Their distance is at most D. Every good row in the lower half lies within D of u, and every good row in the upper half lies within D of v. Hence the difference rules connect all of G and give
\[
 c(y)=\gamma y+\beta\qquad(y\in G).
\tag{2}
\]
Balance excludes \(\gamma=0\), because then one row block would contain all of G, whose size is at least \(0.90h\). Thus \(\gamma=1\).

It follows that \(A_0\) is contained in one physical parity class \(P_0\), and \(A_1\) is contained in the other, \(P_1\). This is exact parity purity of the available alphabets, not merely a bound on their distance from parity.

## 4. Each row block contains its entire physical parity class

Fix i, and identify \(P_i\) with \([1,n]\), where \(2n\le h+1\). If \(r\in P_i\setminus B_i\), the sumsets \(A_i+A_i\) and \(r+A_i\) intersect: they both lie in \([2,2n]\), while
\[
 |A_i+A_i|+|r+A_i|\ge3|A_i|-1>2n-1.
\]
Thus \(r=a+c-b\) for a,b,c in \(A_i\), with \(a\ne b,c\ne b\), since otherwise \(r\in A_i\).

Return to physical row coordinates. The two row differences are nonzero and even. Choose horizontal side differences
\[
 2,\qquad -(a-b)(c-b)/2.
\tag{3}
\]
Both are even, so the three black columns and the completion column all have the same column parity. Translate them to columns of parity i. The only possible collision between two black columns in (3) would require \((a-b)(c-b)=-4\), which forces \(a-b=-(c-b)=\pm2\) and therefore \(r=b\in A_i\), already excluded. The case with product \(+4\) is a valid diamond: the completion shares the central column, while the three black columns are distinct.

The rectangle thus gives a singleton axis rival at row r, contradicting the hypothesis. Therefore \(P_i\subseteq B_i\). Since the two row blocks are disjoint and the two physical parity classes cover the strip, \(B_i=P_i\) for both i.

This settles period-two stability with the stated density. It does not classify period-four or general varying-column alphabets, and it does not assert full validity of these boxes: the remaining four- and six-cell obstructions still occur.
