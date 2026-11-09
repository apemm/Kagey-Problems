# Exact relative pressure for finite protected-law islands

9 November 2026. Rescaling the local wall family gives a relative count for a single protected-law island nearly as long as the full sea memory. The old bulk can be restored by deleting only the island's changed phase columns.

Fix a protected row law \(c_0\), a matched base column law X, and a different matched law Y. On an interval I of length ell, replace X by Y, leaving X elsewhere. The actual error set is
\[
 S=\{j\in I:X(j)\ne Y(j)\}.
\]
Discard descriptions with S empty. All partition functions use the normalized fixed-final-F language.

## 1. A wall family at geometric scale d

For \(d\le c_0'h\), use comparable primitive directions with both physical side lengths of order d. The two side scales are multiples of four. The rectangle has span \(O(d)\), and its vertical translation still has \(\Theta(h)\) choices.

At each dyadic direction scale, there are \(\Theta(d^2)\) direction/side-scale pairs. There are \(\Theta(\log d)\) direction scales and \(\Theta(d)\) horizontal translations isolating the completion across the wall. Thus the event count is
\[
 \Theta(hd^3\log d),
\]
and its unmarked probability mean is
\[
 \Theta(d^3\log d/h^2).
\tag{1}
\]

One fixed black point belongs to \(O(d^2\log d)\) shapes. Two fixed black points have \(O(d)\) eligible completions within the local vertical range. Their conditional masses are therefore
\[
 O(d^2\log d/h^2),\qquad O(d/h).
\]
Mark each event independently with probability
\[
 \theta_d=\frac{b}{1+(d/h)^2\log d}
\]
for a small absolute b. Raw and conditional neighbor sums are then small. The marked mean is at least a constant times
\[
 W_h(d)=\frac{d^3\log d}{h^2+d^2\log d}.
\tag{2}
\]
All constants are absolute, for sufficiently large d.

## 2. One island and exact bulk restoration

Choose
\[
 d=c_1\min(\ell,h)
\]
with sufficiently small absolute \(c_1>0\). Use only the island's left wall. Its three required black corners lie in the preceding X region, and its completion lies in I. The right boundary is outside every chosen geometry.

Distinct matched laws differ on a fixed positive fraction of residues modulo four. Thus a fixed fraction of these completions are wrong-class points under Y, producing genuine singleton rivals.

Retain old X-bulk certificates whose required black columns avoid S. They have the same joint law in the new product space. The conditional lower-probability argument applies to the marked wall events after this retained bulk: its geometric extension pressure is still \(O_\epsilon(h^{-1+\epsilon})\).

Restore the removed old bulk at cost \(C|S|\Lambda^4/h\), where \(\Lambda=1+\log h\). The alphabet cardinality ratio costs only \(O(|S|/h)\). Therefore
\[
 \frac{Z_{X\to Y\to X}(m;I)}{Z_X(m)}
 \le
 \exp[-aW_h(c_1\min(\ell,h))+C\ell\Lambda^4/h].
\tag{3}
\]
Finite end collars sufficient for the chosen roots and bulk model are understood. This is an exact reference comparison, with no bulk-pressure approximation.

For any fixed A and
\[
 h/\Lambda^A\le\ell\le h,
\]
the negative term dominates restoration. It is bounded below by a constant times
\[
 \min\{\ell^3\log\ell/h^2,\ell\}.
\tag{4}
\]
For
\[
 h\le\ell\le c_2h^2/\Lambda^4,
\]
choose the absolute \(c_2>0\) small enough that restoration uses at most half the marked wall mean. The resulting relative cost is at most \(e^{-a'h}\).

## 3. All island lengths up to the near-memory cutoff

For \(\ell\le h/\Lambda^3\), the
[short-packet theorem](polylogarithmic_packet_separation.md)
gives
\[
 \frac{Z_{X\to Y\to X}(m;I)}{Z_X(m)}
 \le e^{-a|S|\log^2(h/\ell)}.
\tag{5}
\]
Its fixed-description estimate does not require an internal-density assumption. For ell at least a fixed constant, distinct matched laws give \(|S|\ge\ell/4\). For smaller nontrivial islands, \(|S|\ge1\).

Equations (3)--(5) cover every nontrivial island with
\[
 1\le\ell\le c_2h^2/\Lambda^4.
\]
Their relative cost is uniformly at most \(\exp(-a_0\log^2h)\), after decreasing \(a_0\).

The lower endpoint of the wall range, \(\ell=h/\Lambda^3\), already has wall penalty of order \(h/\Lambda^8\), which is much larger than \(\log^2h\). Thus no gap remains between the packet and wall estimates.

## 4. Many long islands with short protected gaps

Suppose every island has length
\[
 h/\Lambda^3\le\ell_i\le c_2h^2/\Lambda^4,
\]
and consecutive islands are separated by X-gaps of length at least \(C_3h\), with a sufficiently large absolute \(C_3\). The laws inside islands may differ.

For each island use the preceding left-wall family. Its black variables lie entirely in the preceding X-gap. Different families therefore have disjoint black-variable sets, even when the islands are closer than the full sea memory. Marks are independent.

Retain old bulk avoiding all error columns. The joint raw and conditional bounds have no island-count factor. Restore the old bulk with total cost \(C\sum_i\ell_i\Lambda^4/h\), and absorb it separately in each island's wall mean. This gives
\[
 \frac{Z_{\rm islands}(m)}{Z_X(m)}
 \le
 \exp\left[-a\sum_i
 W_h(c_1\min(\ell_i,h))\right]
\tag{6}
\]
for each fixed island description.

The minimum exponent per island is \(\Omega(h/\Lambda^8)\). There are only polynomially many possible lengths and finitely many matched island laws. Overcounting island starts independently yields the entropy upper bound
\[
 \rho_{\rm long\ islands}
 \le \rho_X\left(1+e^{-a_1h/\Lambda^8}\right).
\tag{7}
\]

If arbitrary short islands are also included but all islands are separated by full-memory collars, their packet and wall families can be combined. Summing all lengths gives instead
\[
 \rho_{\rm isolated\ islands}
 \le\rho_X\left(1+e^{-a_2\log^2h}\right).
\tag{8}
\]

This does not determine the free energy of a semi-infinite wall or an island longer than the stated cutoff. It also does not cover arbitrary internal phase patterns in the long islands. The complete argument passed [independent review](finite_island_pressure_independent_audit.md).

