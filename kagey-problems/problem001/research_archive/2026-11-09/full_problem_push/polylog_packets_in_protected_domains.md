# Polylogarithmically dilute packets inside protected domains

9 November 2026. A variable primitive-direction cutoff lets the polylogarithmic packet estimate coexist with protected domain walls. Packet activities near walls sum to \(o(h)\) per wall, which the actual wall roots absorb.

This note uses the audited
[polylogarithmic packet estimate](polylogarithmic_packet_separation.md).
The combined argument passed [independent review](polylog_packet_independent_audit.md) and a [second audit](polylog_packets_independent_audit.md).

## 1. The language and the two conclusions

Put \(\Lambda=1+\log h\). Fix any constant \(B_0>0\). The base column profile consists of matched protected laws on domains of length at least \(C_0h\), with distinct adjacent laws. End domains may be shorter.

The actual phase flips \(S_i\subseteq I_i\), where
\[
 \ell_i=|I_i|\le h/\Lambda^3,\qquad
 |S_i|\ge\max(1,\lceil\ell_i/\Lambda^{B_0}\rceil).
\tag{1}
\]
The intervals \(I_i\), enlarged by \(\Lambda^{10}\ell_i\) on either side, are disjoint. Error patterns within each packet may be arbitrary.

Let \(c_0\) be the protected row law. If c is balanced and differs from \(c_0\) on r rows, put
\[
 P_h(r)=\frac rh\log^2(h/r).
\]

**Row comparison.** For absolute \(R_0,\delta_0,a>0\), sufficiently large h, and \(R_0\le r\le\delta_0h\), the language has growth
\[
 \log\rho(c)\le
 \log\lceil h/2\rceil-aP_h(r)
       +\exp[-c_{B_0}\log^2h].
\tag{2}
\]
It is therefore strictly below the best protected reference entropy whenever \(r\ge K(1+\log h)^2\).

**Leading pressure at the protected row law.** If \(c=c_0\), then
\[
 \log\rho(c_0)=
 \max_X\log\rho_{c_0,X}
 +o(\log^4h/h).
\tag{3}
\]
These statements concern the specified language, not the full sea shift.

## 2. Guard packets

Put \(H=h\Lambda^8\). A packet is a guard packet if it lies within distance H of a wall or word end. Assign it to one such wall or end.

A packet expansion has radius at most
\[
 \Lambda^{10}\ell_i\le h\Lambda^7=o(H).
\]
The disjoint expansions of all packets near a fixed wall fit in an interval of length \(O(H)\). Their total original width is therefore
\[
 O(H/\Lambda^{10})=O(h/\Lambda^2).
\tag{4}
\]
Counting all possible guard error subsets in that interval, ignoring their actual packet structure, costs at most
\[
 \exp\left[
 O\left(\frac h{\Lambda^2}\log(e\Lambda^{10})\right)\right]
 =\exp[o(h)]
\tag{5}
\]
per wall. Overlapping wall neighborhoods only produce harmless overcounting.

Guard errors remove \(o(h)\) from the marked wall mean and from any bounded-per-error row-root estimate. The wall cost \(ch\) absorbs these losses and the description count.

## 3. Cut off each active packet at its distance from a wall

For an active packet, let \(D_i>H\) be its distance from the nearest wall or end. Choose the primitive cutoff
\[
 R_i=
 \left\lfloor
 \min\left(\frac h{C A\ell_i\Lambda},
           \frac{D_i}{C h}\right)
 \right\rfloor
\tag{6}
\]
with a sufficiently large absolute C. Use the same far-black scale ranges as in the packet proof.

Every retained geometry has horizontal span at most \(D_i/2\), so it stays inside the packet's protected domain. The cutoff also ensures its shortest horizontal leg greatly exceeds its buffer radius \(A\ell_i\Lambda\). The near-cancellation deletion removes only a fixed small fraction.

The mean per root column is at least
\[
 c\,\min\{\log^2(h/\ell_i),\log^2(D_i/h)\}.
\tag{7}
\]
Both logarithms tend to infinity uniformly: the first is at least \(3\log\Lambda\), and the second is at least \(8\log\Lambda\). Fixed numerical constants in (6) only change c.

The global packet incidence bounds are upper bounds for all primitive cutoffs, so they remain valid for (6). Deleting all packet buffers still costs \(o(1)\) mean per root. If c differs from \(c_0\), deleting E geometry removes an \(O(r/h)\) fraction by the aggregate vertical-translation count.

The same fixed marking and conditional local lemma therefore give the penalty in (7) per active error.

## 4. Sum activities as a function of wall distance

Fix a possible packet start at distance d from the nearest wall, with \(d\ge H\). Since \(\ell_i\le h/\Lambda^3=o(d)\), the packet distance \(D_i\) and d differ by a negligible relative amount. Define
\[
 t=\log(d/(C'h)),\qquad s_\ell=\log(h/\ell).
\]
The activity at that start is bounded by
\[
 \sum_{\ell\le h/\Lambda^3}
 \sum_{q\ge\max(1,\lceil\ell/\Lambda^{B_0}\rceil)}
 \binom{\ell}{q}
 e^{-cq\min(s_\ell^2,t^2)}.
\]
Use
\[
 e^{-\min(A,B)}\le e^{-A}+e^{-B}.
\]
The first part is at most \(\exp(-c_1\log^2h)\), by the internally dense packet estimate.

For the second part, \(t\ge c_2\log\Lambda\), so \(ct^2\) dominates the binomial entropy \(1+B_0\log\Lambda\). Summing q first and then ell gives
\[
 C\Lambda^{B_0}e^{-c_3t^2}.
\]
Indeed, lengths up to \(\Lambda^{B_0}\) contribute at most that bound, while the larger lengths form a geometric tail in \(\ell/\Lambda^{B_0}\). Thus the total per-start activity is at most
\[
 e^{-c_1\log^2h}
 +C\Lambda^{B_0}
   e^{-c_3\log^2(d/(C'h))}.
\tag{8}
\]

The second term is an interface decoration. For one wall its sum over \(d\ge H\) is bounded by
\[
 Ch\Lambda^{B_0}
 \int_{\Lambda^8/C'}^\infty e^{-c_3\log^2u}\,du
 =o(h).
\tag{9}
\]
Set \(v=\log u\); the tail is the integral of \(e^{v-c_3v^2}\), which decays faster than any power of \(\Lambda\). The nearest-wall contribution is at most the sum of the contributions of all walls.

Allowing a packet to start at each column therefore costs at most
\[
 \exp\bigl[m e^{-c_1\log^2h}+o(h)J+O_h(1)\bigr].
\tag{10}
\]
The \(o(h)J\) term is absorbed by the marked wall roots.

## 5. Combine with row pressure

Jointly use adaptive row roots, marked wall roots, and marked active packet roots. Their cross-family one- and two-assignment bounds are the established ones. Three shared assignments are impossible: row completions are in E; wall and packet completions avoid E; packet completion columns are errors, whereas wall completions avoid errors.

The row-root mean is
\[
 aP_h(r)m-C\sqrt{rh}(J+1)-C|S|,
\]
with a bounded coefficient on the error term. Guard errors are controlled by (4). Active packet penalties in (7) tend to infinity per error, so they absorb their row-root loss while retaining a fixed fraction of their own penalty.

Choose \(\delta_0\) small to absorb \(C\sqrt{rh}J\) into the marked wall mean. The absolute product-space count then has simultaneous losses \(aP_h(r)m\), \(chJ\), and the active-packet penalty. Equations (5), (9), and (10) pay all packet descriptions. The remaining wall descriptions have activity \(e^{-ch}\). This proves (2).

## 6. Preserve the leading protected pressure

When E is empty, use the truncated bulk from
[the leading-domain proof](protected_domain_leading_pressure.md):
for fixed \(\delta>0\), its span is \(O(h^{2-\delta})\), and its omitted mean is
\(O(\delta\log^4h/h)+o_\delta(\log^4h/h)\).

Avoid that bulk first, then the marked active packet roots. Their conditional estimate preserves the coefficient one on the retained bulk mean. The packet penalty (7) absorbs bulk deleted at active errors, whose cost is only \(O(\log^4h/h)\) per error.

Guard errors have total size \(O(hJ/\Lambda^2)\), so their deleted bulk costs \(O(J\Lambda^2)\). Their descriptions and the distance-dependent active activities cost \(o(h)J\). At wall density \(J/m\le A\Lambda^4/h^2\), all these are \(o(\Lambda^4/h)\), as is the truncated cut loss.

At larger wall density, the absolute wall/packet count excludes competition with protected pressure. Fix delta, let h tend to infinity, then let delta decrease to zero. This proves (3).

The ordinary domain-and-packet language in this theorem is therefore strictly below the quadratic protected phase once the proved protected ordering is used. Full ordinary-parity component dominance remains outside the statement.

