# Stability of near-half Cartesian boxes of column period four

9 November 2026. This gives an exact local classification of the row partition and column phase for dense period-four alphabets. The complete argument passed independent review. It does not classify general sea components.

Let \(h\ge1000\), let \(B_0,B_1\) be a balanced row partition, and let \(A_0,A_1,A_2,A_3\) satisfy
\[
 |A_j|\ge0.49h,\qquad A_j\subseteq B_{t_j},\qquad t_j\in\mathbb F_2.
\]
Use \(A_j\) at columns congruent to j modulo four. Suppose no assignment in this Cartesian box has a singleton-axis rival relative to \(B_0\times B_1\).

Up to column translation and exchange of row-block labels, the possibilities are:

- \(t=0000\): the used block contains one whole ordinary parity class and at most one extra row; the extra row is excluded if vertical-pair rivals are also forbidden.
- \(t=0101\): the row partition is exactly ordinary parity, and every alphabet follows its checkerboard column class.
- \(t=0011\): writing \(q(n)=n(n-1)/2\bmod2\), the row coloring is exactly \(c(y)=q(y)+\gamma y+\beta\), and the alphabets follow the corresponding quadratic protected law.

The remaining phase type \(0001\), including its rotations and complement, is impossible. In the quadratic case, balance retains the restrictions in [separable_rectangle_xor_classification.md](separable_rectangle_xor_classification.md): \(q(y)+y\) is excluded when \(h\equiv2\pmod4\).

All witnesses have horizontal span \(O(h^2)\). A periodic Cartesian window of width \(2h^2+10\), with the fixed complete pair set used for virtual axis rivals, already suffices.

## 1. Intersections provide common good rows

For each used block i, intersect the alphabets at its occurrences and call the result \(C_i\). A row of \(C_i\) is available at every column residue whose phase is i. The smaller Cartesian box using these intersections is singleton-free, as are all its horizontal translations.

For phase \(0000\), the common intersection has size at least
\[
 4(0.49h)-3\lceil h/2\rceil\ge0.46h-1.5>\lceil h/3\rceil.
\]
The sharp constant-alphabet theorem applies.

For phase \(0101\), both intersections have size at least \(0.48h-0.5\). Apply [period_two_alphabet_stability.md](period_two_alphabet_stability.md), whose density threshold is \(0.45h\).

It remains to consider \(0011\) and \(0001\). Put \(G=C_0\cup C_1\) and \(e=h-|G|\). The intersections give
\[
 e\le0.04h\quad\text{for }0011,\qquad
 e\le0.04h+1\quad\text{for }0001.
\tag{1}
\]
Let \(c(y)=i\) on \(B_i\).

We repeatedly use the elementary dense partial-Freiman lemma proved in Section 3 of the period-two note: if \(G\subseteq[1,H]\) misses at most \(0.10H\) rows, \(H\ge100\), and a function f on G obeys
\[
 f(a)+f(a+d)+f(y)+f(y+d)=0
\tag{2}
\]
whenever all four rows are good and \(d(y-a)\notin\{0,1,-1\}\), then f is affine on G. The proof compares good pairs at each distance up to \(H/2\), uses good triples to add differences, and connects the two halves through good middle anchors. It does not require either fiber of f to be balanced.

## 2. The quadratic phase determines c on the good rows

Normalize \(0011\) as \(t_x=q(x)\). A translation by two columns complements this phase. For four good rows \(a,a+d,y,y+d\), use sides
\[
 (1,d),\qquad(-d(y-a),y-a),
\]
whose corner columns are distinct under the exception in (2).

The four-corner sum of the column phase q equals \(d(y-a)\) modulo two. If the sum of the row colors differed from that value, one of the two complementary translated boxes would allow exactly three corners, producing a singleton rival. Hence \(f(y)=c(y)+q(y)\) satisfies (2). By the dense lemma,
\[
 c(y)=q(y)+\gamma y+\beta\qquad(y\in G).
\tag{3}
\]

## 3. The quadratic rule extends to every row

Suppose some row r violates (3). Choose a completion point \(W=(x,r)\) whose column phase equals the predicted value \(q(r)+\gamma r+\beta\). Count rectangles through W with sides parallel to \((1,1)\) and \((1,-1)\).

Write their other row increments as a,b, so the four rows are
\[
 r,\quad r+a,\quad r+b,\quad r+a+b,
\]
and take adjacent vectors \((a,a)\), \((-b,b)\), with \(a,b\ne0\). Put \(H_-=r-1\), \(H_+=h-r\). The number of all such in-strip rectangles is exactly
\[
 D_0=\frac{H_+(H_+-1)+H_-(H_--1)}2+2H_+H_-
     =\frac{(h-1)(h-2)}2+H_+H_-.
\tag{4}
\]

For the predicted cell law \(q(x)+q(y)+\gamma y+\beta=0\), compatibility requires one of a,b to be even, with the choice determined by W's parity. The other increment is unrestricted. The counting region is symmetric in a,b; imposing either parity condition retains at least \(D_0/2-(h-1)\) choices. Excluding \(a=b\) and \(a=-b\) removes at most \(2(h-1)\) further choices and guarantees four distinct corner columns. Thus at least
\[
 h^2/4-4h
\tag{5}
\]
phase-compatible four-distinct-column rectangles remain.

For any one excluded row \(s\notin G\), at most \(3h\) of these rectangles use s among the three non-W corners: fix a, fix b, or fix a+b. By (1), deleting all bad rows loses at most \(0.12h^2\) choices. The remainder is positive for \(h\ge1000\).

The three surviving corners have good rows, so their actual block colors agree with the predicted law and they are available in the appropriate \(C_i\). The completion W has the opposite actual block color by assumption. This realizes a singleton axis rival. The contradiction proves (3) for every row, and every original alphabet consequently follows the exact quadratic law.

## 4. The three-to-one column phase forces a period-four row template

Normalize the remaining type as \(t=0001\). For any rectangle whose horizontal side differences are even, its corner columns use at most two residue classes modulo four. Rotations of \(0001\) realize both split colorings on the two residues of either fixed horizontal parity: put the unique minority phase on either residue. These two restrictions are complements and are affine in the rescaled column coordinate \(x/2\).

Fix one physical row parity. Rescale its row positions to an interval \([1,n]\), where \(n\ge(h-1)/2\). Four good rescaled rows \(a,a+d,y,y+d\) are realized by physical side vectors
\[
 (2,2d),\qquad(-2d(y-a),\,2(y-a)).
\tag{6}
\]
The four columns are distinct under the exception in (2). The two split column colorings just described have even four-corner XOR. Singleton exclusion therefore forces the row coloring, restricted to this physical parity, to obey (2).

The number of bad rows in either parity interval is at most \(0.04h+1<0.10n\). The dense lemma applies to each parity separately. Consequently c agrees on G with some function of the physical row modulo four.

Balance forces that template to take value one on exactly two of the four residue classes. Otherwise one actual row block contains all good rows in at least three residue classes, and thus has at least
\[
 3\lfloor h/4\rfloor-e\ge0.71h-4>\lceil h/2\rceil
\]
rows. The six balanced binary templates modulo four are precisely the two ordinary parity templates and the four quadratic templates \(q(y)+\gamma y+\beta\).

## 5. Neither row-template type can coexist with 0001

If the good-row template is ordinary parity, use sides \((1,2),(2,-1)\). Put the unique minority column phase at the fourth column. For either ordinary parity labeling, at least \(h/2-O(1)\) vertical translations have three allowed corners and a completion in the opposite row block. Requiring all four rows to be good removes at most \(4e\le0.16h+4\) translations, so a singleton rival remains.

If the good-row template is quadratic, it has one occurrence of the row pattern \(1,0,0\) per four rows. Place the center of a unit diamond in the unique minority column and its two outer black corners in the adjacent majority columns:
\[
 (x,b),\qquad(x-1,b+1),\qquad(x+1,b+1),
\]
with white completion \((x,b+2)\). Choose a row triple whose predicted colors are \(1,0,0\). There are at least \(h/4-O(1)\) choices, and excluding bad rows loses at most \(3e\le0.12h+3\). A good triple remains. Its three black columns are distinct, and the white completion shares the center column with a black row of the opposite block. This is again a singleton axis rival.

Both possibilities contradict the hypothesis, excluding \(0001\). The classification is complete.

These are product-box stability results. They do not imply that a general high-entropy recurrent component contains such a box, and they do not remove the four- or six-cell obstructions from the classified boxes.

