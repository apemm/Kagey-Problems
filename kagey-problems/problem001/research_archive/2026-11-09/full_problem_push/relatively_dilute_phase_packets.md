# Exact pressure for relatively dilute short packets

9 November 2026. The isolated-packet comparison extends to packets whose event neighborhoods overlap. Separation is required only relative to packet width, with a subpolynomial factor. An explicit divisor majorant also permits packet widths \(h^{1-o(1)}\).

Fix a protected pair \((c_0,X)\) and its normalized fixed-final-F partition functions. Let \(L=Ch^2\) bound complete support spans. Set
\[
 M_h=\left\lceil4(L+h^2)^2\right\rceil,\qquad
 T_h=\max_{1\le n\le M_h}\tau(n).
\]
Choose an absolute constant \(C_0\) large enough that
\[
 U_h=\left\lceil
 \exp\left(C_0\frac{\log h}{\log\log h}\right)
 \right\rceil\ge T_h
\tag{1}
\]
for all sufficiently large h. This is the elementary divisor bound already proved in [the spacing note](polynomially_spaced_parity_defects.md). Write \(\Lambda=1+\log h\), and put
\[
 g_h=U_h\Lambda^3,\qquad
 \ell_{\max}=\left\lfloor\frac h{U_h\Lambda^2}\right\rfloor.
\tag{2}
\]

Let \(I_i\) be integer intervals of lengths \(\ell_i\le\ell_{\max}\), and require their enlarged intervals
\[
 J_i=I_i+[-g_h\ell_i,g_h\ell_i]
\tag{3}
\]
to be pairwise disjoint. Choose arbitrary \(S_i\subseteq I_i\), and set \(S=\bigcup_iS_i\). The actual phase is \(X+1_S\). Assume the packets are at distance at least L from the finite word ends.

**Relative-dilution claim.** There is an absolute c such that
\[
 Z_{X,S}(m)\le Z_X(m)
 \exp\left[-c\sum_i|S_i|\log^2(h/\ell_i)\right].
\tag{4}
\]
The error patterns within packets may be arbitrary. The complete proof passed [independent review](isolated_packets_independent_audit.md).

The event neighborhoods may overlap: the condition in (3) is much weaker than full-memory isolation. Since \(g_h=h^{o(1)}\), its required gap is a subpolynomial multiple of packet width.

## 1. Construction and an absolute incidence kernel

For each packet define
\[
 B_i=A\ell_i\Lambda,\qquad
 R_i=\left\lfloor\frac h{1000B_i}\right\rfloor,
\qquad
 V_i=I_i+[-B_i,B_i],
\tag{5}
\]
with large absolute A. Use the far-black construction from
[isolated short packets](isolated_short_phase_packets.md), then remove every event having a prescribed black column in any \(V_j\).

Before the additional removals, each root column in \(S_i\) has mean at least \(c\log^2R_i\). The width bound gives
\[
 R_i\ge cU_h\Lambda,\qquad
 \log R_i\ge\tfrac12\log(h/\ell_i)
\tag{6}
\]
for large h.

The refined completion-column kernel has the absolute form
\[
 K_h(d)\le C\left[
 \frac{\tau(d)}d+\frac{T_h}{\max(h,d)}
 \right],\qquad 1\le d\le L.
\tag{7}
\]
This bounds raw incidence at a free column from one completion column. It also bounds the compatible extension mass after fixing one prescribed black point. The norm and factorization integers in its proof are at most \(M_h\), so replacing all divisor estimates by \(T_h\) is legitimate.

## 2. A packing estimate

Fix a real point x. Apart from at most one packet whose \(J_i\) contains x, every packet satisfies
\[
 D_i=\operatorname{dist}(x,I_i)\ge g_h\ell_i.
\]
For these far packets, take the central half of \(J_i\), obtained by enlarging \(I_i\) by \(g_h\ell_i/2\). Its length is comparable to \(g_h\ell_i\), and its distance from x is comparable to \(D_i\). These central intervals are disjoint.

For packets with \(D_i\le L\), the central intervals lie within distance \(2L\) of x for large h. Indeed \(g_h\ell_i\le h\Lambda=o(L)\). Integrating \(1/|t-x|\) over them gives
\[
 \sum_{\mathrm{far},\,D_i\le L}\frac{\ell_i}{D_i}
 \le C\frac{\Lambda}{g_h}.
\tag{8}
\]
The lower integration cutoff is at least \(g_h/2\), because \(\ell_i\ge1\).

The same argument, split at \(D_i=h\), gives
\[
 \sum_{\mathrm{far},\,D_i\le L}
 \frac{\ell_i}{\max(h,D_i)}
 \le C\frac{\Lambda}{g_h}.
\tag{9}
\]
For \(D_i<h\), the disjoint central intervals have total length \(O(h)\), so their total original length is \(O(h/g_h)\).

Both estimates remain valid with the cutoff \(2L\) in place of L, after changing their absolute constants.

## 3. Global one-cell incidence

Any prescribed black point used in the retained construction is outside every \(V_i\). If a near packet has \(x\in J_i\), its distance is still at least \(B_i\). The interval divisor estimate gives
\[
 \sum_{j\in I_i}\frac{\tau(|x-j|)}{|x-j|}
 \le C/A+o(1).
\tag{10}
\]
Its diagonal contribution is at most
\[
 T_h\ell_i/h\le1/\Lambda^2.
\tag{11}
\]

For all far packets, use \(\tau(d)\le T_h\) and (8)--(9). Their total kernel is at most
\[
 C T_h\Lambda/g_h\le C/\Lambda^2.
\tag{12}
\]
Thus the raw incident weight at every used column, and the compatible mass through one prescribed black cell, are at most \(C/A+o(1)\). There is no factor depending on the number of packets.

## 4. The other buffers remove negligible mean

Fix a root column \(x\in S_i\). All other packets are far in the sense of Section 2. Each buffer \(V_j\) has length \(O(A\Lambda\ell_j)\), and every point in it has distance comparable to \(D_j\), since \(g_h\gg A\Lambda\). Only black columns within distance L of x can occur. Thus only buffers with \(D_j\le2L\) contribute, and every sum in (13) is restricted accordingly.

Equation (7) and the bound \(K_h(d)\le CT_h/d\) give
\[
 \sum_{j\ne i}\sum_{y\in V_j}K_h(|y-x|)
 \le C A T_h\Lambda
       \sum_{j\ne i}\frac{\ell_j}{D_j}
 \le C A T_h\Lambda^2/g_h
 \le C A/\Lambda.
\tag{13}
\]
This is an upper bound for the mean lost by forbidding other buffers as black columns. The own-packet buffer was already excluded by construction. Hence every root retains mean at least
\[
 c\log^2(h/\ell_i).
\tag{14}
\]

## 5. Joint conditional avoidance and restoration

Two prescribed black cells in distinct columns have only \(O(h)\) possible completion points anywhere in the strip. The completion loci are nonhorizontal perpendicular lines or Thales circles; axis degeneracies are excluded. Their total conditional mass across all root columns is therefore \(O(1)\).

Mark every retained root event by a sufficiently small absolute probability theta. The one-cell bound in Section 3, the two-cell \(O(1)\) bound, and uniqueness of a three-cell completion give small raw and conditional neighbor sums. Old protected bulk events have their previously established vanishing extension pressure.

Retain old bulk certificates whose black columns avoid S. Apply the joint local lemma, list those bulk events first, and then use the exact conditional lower-probability bound for the marked roots. The resulting extra cost is
\[
 \exp\left[-c\sum_i|S_i|\log^2(h/\ell_i)\right].
\]
The constant marking rate changes only c.

Restoring the deleted old bulk costs at most \(\exp(C|S|\Lambda^4/h)\). The selected-alphabet cardinality ratio is at most \(\exp(C|S|/h)\). Both are absorbed because
\[
 \min_i\log^2(h/\ell_i)
 \ge c\frac{\log^2h}{(\log\log h)^2},
\]
whereas \(\Lambda^4/h\to0\). This proves (4).

## 6. Sum arbitrary packet descriptions

For a fixed interval of length ell, the weight of all nonempty error subsets is at most
\[
 a_\ell=
 \left(1+e^{-c\log^2(h/\ell)}\right)^\ell-1.
\]
For \(\ell\le\ell_{\max}\),
\[
 \sum_{\ell\le\ell_{\max}}a_\ell
 \le
 \exp\left[-c'\frac{\log^2h}{(\log\log h)^2}\right].
\tag{15}
\]
Indeed \(a_\ell\le2\ell e^{-c\log^2(h/\ell)}\) for large h, and the polynomial number and size of the possible lengths are absorbed by the exponent.

Overcount allowed packet collections by permitting any interval length to start at every column, without imposing (3) in the weighted sum. Every actual admissible packet decomposition occurs in this larger sum. The union language therefore has growth rate at most
\[
 \rho_X(h)\left(
 1+\exp\left[-c'\frac{\log^2h}{(\log\log h)^2}\right]\right).
\tag{16}
\]
End packets can be discarded at a fixed-height cost.

If packet widths are restricted to \(h^{1-\delta}\), the error term improves to \(\exp(-c_\delta\log^2h)\).

The remaining profiles have packets whose relative separation fails (3), or whose widths exceed the stated range. The theorem does not imply general boundary-component dominance.

