# Partial stability for approximate reflection closure

9 November 2026. The short-step conditions give an exact decomposition into simple row intervals. Long-distance conditions also align parity domains when the number of domain boundaries is controlled. Both arguments passed independent review. These are partial stability statements; they do not yet prove that every approximately closed balanced block is close to parity.

Let \(c:[1,h]\to\{0,1\}\) be balanced, fix \(s\in\{0,1\}\), and put \(A=\{a:c(a)=s\}\). Define
\[
 n_s(k)=\#\{a\in A:a\pm k\in[1,h],\
                         c(a-k)\ne c(a+k)\},
 \qquad V_s=\sum_{k\ge1}n_s(k).
\]
The near-full box dichotomy in [full_row_class_phase_classification.md](full_row_class_phase_classification.md) supplies \(n_s(k)\le2M\) for every k in its approximate-closure branch. In particular,
\[
 V_s\le Mh,\qquad n_s(1)+n_s(2)\le4M.
\tag{1}
\]

## 1. Short-step defects give a piecewise classification

Put \(v=n_s(1)+n_s(2)\). Delete the row centers a witnessing either of these two types of defect. There are at most v deleted rows. The remaining at most \(v+1\) consecutive intervals each have one of the following forms:

- Every row is in A.
- The A rows are exactly one parity class within that interval.
- The A rows are three-separated, meaning that consecutive A rows differ by at least three.

This is exact, including intervals of small length. To prove it, work in one remaining interval I. If it contains two adjacent A rows, the absence of distance-one defects at A centers propagates A to all of I. Otherwise it contains no adjacent A rows. If it contains an A pair at distance two, the absence of distance-two defects propagates that pair to a full parity class in I. An additional A row would be adjacent to the propagated class, so there is none. If no such pair exists, A is three-separated.

Thus \(O(M)\) short-step defects give \(O(M)\) intervals, but these intervals need not all be parity intervals. Balance does not remove the other alternatives.

For example, at height \(h=4n\), let the indicator of A be
\[
 1^n(100)^n.
\tag{2}
\]
It has exactly \(2n\) ones. All short-step defects lie within two rows of the single interface, so \(n_s(1)+n_s(2)=O(1)\). Yet its constant initial block alone differs from either parity class in at least \(n/2-O(1)\) rows. This prevents a short-step-only conclusion of closeness to a single parity class, or even of closeness to a bounded collection of parity pieces after only \(O(v)\) row changes.

## 2. Long-distance violations align a bounded number of parity domains

Write
\[
 \beta(y)=c(y)+(y\bmod2)\pmod2,
\]
and let w be the number of changes of \(\beta\) between adjacent rows. Thus c is ordinary parity with a fixed choice of phase on each of \(w+1\) intervals. This definition allows intervals of length one.

Let
\[
 r=\min\bigl(|\beta^{-1}(0)|,|\beta^{-1}(1)|\bigr),
\]
the number of row changes needed to make c one ordinary parity coloring. For either choice of s,
\[
 r\le \frac{8V_s}{h}+14w+6.
\tag{3}
\]
In particular, if \(V_s\le Mh\) and \(w=O(M)\), then c is \(O(M)\)-close to one global parity coloring. This controls macroscopic opposite-parity domains, which the short-step defect count alone does not.

To prove (3), let \(n_i=|\beta^{-1}(i)|\), and let \(\delta_i\) be the number of even rows minus the number of odd rows in \(\beta^{-1}(i)\). Each constant-\(\beta\) interval contributes at most one in absolute value, so \(|\delta_i|\le w+1\).

Every unordered pair \(u<v\) of the same physical parity has an integer midpoint and half-gap. If \(c(u)\ne c(v)\), it contributes once to \(V_0+V_1\), according to the midpoint's color. Consequently
\[
 V_0+V_1
 =\frac{n_0n_1+\delta_0\delta_1}{2}
 \ge\frac{n_0n_1-(w+1)^2}{2}.
\tag{4}
\]

Next shift such a pair one row to the right. Unless an endpoint or its midpoint crosses a \(\beta\)-boundary, both endpoint colors and the midpoint color flip. The pair remains a mismatch, but its contribution switches between \(V_0\) and \(V_1\). The shift is injective. At most \((3w+1)h\) pairs are exceptional: a boundary can occur at either endpoint or at the midpoint, and the right edge of the board contributes at most h more pairs. Applying the same injection in each direction gives
\[
 |V_0-V_1|\le(3w+1)h.
\tag{5}
\]
It follows that
\[
 V_s\ge \frac{n_0n_1}{4}
          -\frac{(w+1)^2}{4}
          -\frac{(3w+1)h}{2}.
\]
Since \(n_0n_1=r(h-r)\ge rh/2\), and \(w+1\le h\), rearrangement gives (3).

## 3. A condition stated directly in terms of one row block

Let p be the number of adjacent A pairs. In any balanced binary row word, the numbers of adjacent pairs of the two colors differ by at most two. Indeed the number of adjacent pairs of color s is its number of rows minus its number of runs, and the two run counts differ by at most one.

An adjacent pair has equal c-colors precisely when \(\beta\) changes. Therefore
\[
 w\le2p+2.
\]
Equation (3) gives the convenient bound
\[
 r\le \frac{8V_s}{h}+28p+34.
\tag{6}
\]
Thus approximate reflection closure together with \(O(M)\) adjacent pairs in one balanced block implies \(O(M)\) distance from ordinary parity.

The remaining problem is to control the dense constant intervals and sparse intervals from Section 1 using the long-distance estimates in (1). The bound \(V_s\le Mh\) is plausibly strong enough to do so, but no unconditional \(O(M)\) or \(O(\sqrt{Mh})\) global stability estimate is asserted here.

## 4. A concrete unresolved inequality

Let \(e=|A\cap2\mathbb Z|\), \(o=|A\setminus2\mathbb Z|\). When \(h=2n\) and \(|A|=n\), the exact endpoint count gives
\[
 V_A+V_{A^c}=e(n-e)+o(n-o)=2eo.
\tag{7}
\]
The unresolved issue is whether one of these two counts can be an arbitrarily small fraction of their sum for balanced sets at large height.

A uniform inequality
\[
 V_A\ge c\,eo
\tag{8}
\]
with an absolute \(c>0\) would imply the desired unconditional linear stability. At even height, distance to the nearer parity class is \(r=2\min(e,o)\), and \(eo\ge rh/8\). Thus (8) would give \(r\le8V_A/(ch)\), with no adjacency hypothesis. The analogous odd-height conclusion has an additive constant.

The exact finite probe [reflection_even_odd_probe.json](reflection_even_odd_probe.json) checked all balanced blocks through height twenty. For \(8\le h\le20\), its minimum \(V_A/(eo)\) was at least \(1/4\), with equality at height eight. At height seven, \(\{1,4,7\}\) gives zero, as expected. These checks suggest (8), but do not prove a uniform positive constant or the value \(1/4\).

