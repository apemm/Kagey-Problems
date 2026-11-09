# Joint pressure for protected domains with dilute packets

9 November 2026. The separated-domain row comparison allows a collection of relatively dilute phase-error packets without any bound relating their total error density to the row distance. Packets near interfaces are paid for by the wall cost. Packets farther away have their own large rooted-event penalty.

Use the notation \(U_h,\Lambda,g_h,\ell_{\max}\) from
[relative packet dilution](relatively_dilute_phase_packets.md):
\[
 U_h=\exp\left(O\left(\frac{\log h}{\log\log h}\right)\right),
 \quad g_h=U_h\Lambda^3,\quad
 \ell_{\max}=\left\lfloor h/(U_h\Lambda^2)\right\rfloor.
\]
Fix a protected row law \(c_0\), and a balanced row law c differing in r rows. Let
\[
 P_h(r)=\frac rh\log^2(h/r),\qquad
 Q_h=\log^2U_h.
\]

The base column phase is a concatenation of matched protected laws, with distinct adjacent laws and minimum domain length \(C_0h\). The first and last domain may be shorter. The actual phase flips arbitrary subsets \(S_i\subseteq I_i\), where \(|I_i|\le\ell_{\max}\), and the intervals enlarged by \(g_h|I_i|\) on each side are pairwise disjoint. There is no prescribed upper bound on the total number of flipped columns.

**Claim.** For absolute \(R_0,\delta_0,a,C>0\), sufficiently large h, and \(R_0\le r\le\delta_0h\), this union language has growth rate satisfying
\[
 \log\rho_{\mathrm{dom+pack}}(c)
 \le\log\lceil h/2\rceil-aP_h(r)+Ce^{-aQ_h}.
\tag{1}
\]
Consequently it is strictly subdominant to the best protected reference whenever
\[
 K(1+\log h)^2\le r\le\delta_0h
\]
for a sufficiently large absolute K. The complete proof passed [independent review](domains_packets_independent_audit.md).

## 1. Guard packets and active packets

Put \(H_h=hU_h\). Call a packet a guard packet if its interval is within distance \(H_h\) of a domain wall, or of a finite word end. Assign each guard packet to one such wall or end. All other packets are active.

Fix a wall. Every packet within distance \(H_h\) has its enlarged interval contained in a region of length \(O(H_h)\), because
\[
 g_h\ell_{\max}\le h\Lambda=o(H_h).
\]
The enlarged intervals are disjoint and have lengths comparable to \(g_h|I_i|\). Hence their total original width is at most
\[
 C H_h/g_h=C h/\Lambda^3.
\tag{2}
\]
This bound also applies to the number of guard errors assigned to the wall. The total guard-error count is therefore \(O(hJ/\Lambda^3)+O_h(1)\), where J is the number of walls.

Given a wall, all assigned guard errors lie in an interval of length \(O(H_h)\). Counting every subset of size at most the bound in (2) gives at most
\[
 \exp\left[
 O\left(\frac h{\Lambda^3}
       \log(eU_h\Lambda^3)\right)\right]
 =\exp[o(h)]
\tag{3}
\]
possibilities. This overcounts packet descriptions, which is harmless. Errors at the two finite ends contribute only a fixed-height factor.

## 2. Rooted events for active packets

For active packets, replace the variable primitive cutoff in the packet proof by
\[
 R_*=\lfloor U_h/C_1\rfloor
\]
for a sufficiently large absolute \(C_1\). Retain its scale ranges
\(k\asymp h/b\), \(t\asymp h/a\), and exclude the near-cancellation band for the opposite corner.

The horizontal span is at most \(H_h/2\). Every active packet is more than \(H_h\) from every wall, so all its root geometries lie within one protected domain. The shortest horizontal side is comparable to \(h/U_h\), whereas every packet buffer has length at most
\[
 A\Lambda\ell_{\max}\le Ah/(U_h\Lambda).
\]
Thus the far-black construction still works. Each active root column has mean at least
\[
 cQ_h.
\tag{4}
\]

Remove geometries with any row in \(E=\{c\ne c_0\}\), including their completion row. A prescribed corner row fixes the vertical translate. The removed fraction is \(O(r/h)\), uniformly over the primitive cutoff. A fixed fraction survives for small \(\delta_0\).

Delete every event with a black column in any packet buffer, including guard-packet buffers. The relative-dilution packing estimate bounds its additional mean loss by \(O(1/\Lambda)\) per root. The global one-cell incidence remains \(C/A+o(1)\), and the two-cell mass is \(O(1)\). Mark this family with a sufficiently small absolute probability. Its total marked mean is at least
\[
 cQ_h|S_{\rm active}|.
\tag{5}
\]

## 3. Combine row, wall, and packet roots

Use the adaptive row roots and marked wall roots from
[the joint domain theorem](separated_domain_partition_comparison.md).
They avoid all actual error columns at their black and completion positions. Their respective means are at least
\[
 aP_h(r)m-C\sqrt{rh}(J+1)
       -CqR\log R\,|S|,
\qquad
 a'hJ-C|S_{\rm guard}|-O_h(1),
\tag{6}
\]
where \(q=r/h\) and \(R=\lfloor q^{-1/2}\rfloor\).

The wall loss only involves guard errors: active packets lie farther than \(H_h\gg h\) from the wall neighborhoods. The coefficient \(qR\log R\) in the row loss is bounded absolutely.

The three families have small joint raw and conditional overlap sums. Their one-cell and two-cell estimates are the established bounds:

- row roots: \(O(qR\log R+q)\);
- marked wall roots: \(O(b_0)\);
- marked packet roots: \(O(\theta)\), after the interval-kernel estimate.

There are no cross-family three-assignment coincidences. Row-root completions lie in E, while wall and packet completions avoid E. Packet completions have columns in S, while retained wall completions avoid S. Three prescribed right-triangle corners determine one completion.

Choose the two marking constants first. Then choose \(\delta_0\) so the row conditional sum is small and the endpoint term \(C\sqrt{rh}J\) is absorbed by a fixed fraction of the wall mean. The active-packet mean absorbs the row loss at active errors because \(Q_h\to\infty\). Equations (2) and (6) show that guard-error losses are \(o(hJ)\), also absorbed by the wall mean.

The exact conditional lower-probability lemma therefore gives, for every fixed domain/packet description,
\[
 Z_c(t)\le C_h\lceil h/2\rceil^m
 \exp[-a_1P_h(r)m-a_2hJ-a_3Q_h|S_{\rm active}|].
\tag{7}
\]
This is an absolute product-space estimate. No old crossing bulk is restored.

## 4. Sum the descriptions

For each wall, (3) counts all possible assigned guard errors at cost \(\exp(o(h))\). This is absorbed by half the \(a_2hJ\) term in (7).

For an active packet of length ell, summing all its nonempty internal error subsets gives weight
\[
 (1+e^{-a_3Q_h})^\ell-1
 \le2\ell e^{-a_3Q_h}.
\]
Since \(Q_h\asymp\log^2h/(\log\log h)^2\gg\log h\),
\[
 \sum_{\ell\le\ell_{\max}}2\ell e^{-a_3Q_h}
 \le e^{-a_4Q_h}.
\]
Allowing any active packet to start at each column overcounts the allowed descriptions and contributes exponential factor at most \(1+e^{-a_4Q_h}\).

Finally, summing the at most \(4^{J+1}\binom{m-1}{J}\) domain descriptions gives a factor \(1+O(e^{-a_5h})\). These bounds prove (1). The protected lower bound \(h/2-O(\log^4h)\) and monotonicity of \(r\log^2(h/r)\) then give the stated \(O(\log^2h)\) residual row distance.

## 5. Scope

The total packet-error density may be much larger than r/h. The theorem replaces the earlier quantitative density restriction by a geometric dilution condition on packet intervals.

It does not cover arbitrary errors within macroscopic domains, densely interacting packets that fail the relative-gap condition, or general boundary-component dominance. Its pressure estimate is absolute; the sign of the relative free energy of a long domain wall remains unresolved.

