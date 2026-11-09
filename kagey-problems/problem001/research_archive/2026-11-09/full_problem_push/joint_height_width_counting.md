# A simultaneous height-width counting bound

9 November 2026. The container argument also counts equality words with double columns. This gives a joint asymptotic regime, in addition to the iterated-limit statement in [sea_entropy_half_container.md](sea_entropy_half_container.md). Independent review checked the slot-fingerprint count, weighted AM–GM, uniform normalization, and the scaffold/core overhead.

Write \(q_h=\lfloor h^2/4\rfloor\), and let \(E_h(m)\) count valid words with exactly \(m+q_h\) black cells. These are maximum blackouts whenever equality is attained. If equality is not attained, \(E_h(m)=0\), and it is not the number \(a_h(m)\) of maximum blackouts.

## 1. Equality black sets avoid the same hypergraph

Every equality word determines a balanced partition \(\pi\), has every edge of \(F_\pi\) as a double column exactly once, and has one black cell in each other column.

Its entire black set is independent in the four-cell hypergraph \(H_\pi\) used in the entropy proof. Suppose it contains three corners of a tilted rectangle and the opposite-class replacement cell in the fourth corner's column. If the fourth corner is black, the rectangle is hidden, which is impossible on boards of height and width at least four. If it is white, the unique double column carrying its pair with the replacement row supplies an actual axis rectangle with the same singleton presentation. This is again invalid. That double column is distinct from the missing corner's column, since the missing corner is white.

The same implication holds for the black cells in any \(h\)-column block of the word. The tilted rectangle is contained in that block; the axis rival can use a double column anywhere in the full board.

## 2. A block with \(d\) doubles

Fix \(\eta>0\), put \(\alpha=1/2+\eta<1\), and use the containers and fingerprints from the entropy proof. Every independent set in the \(h\times h\) block has a fingerprint of size at most
\[
 s_h=O_\eta\bigl(h/(\log h)^{1/3}\bigr),
\]
with remainder container of size at most \(\alpha h^2\).

Fix a set of \(d\) double columns. There are \(h+d\) formal slots, one for each selected cell, using two slots in a double column. The number of size-\(t\) fingerprints is at most
\[
 \binom{h+d}{t}h^t.
\]
This overcounts unordered pairs and any repeated choice in a column, which is harmless.

After a fingerprint is fixed, let \(r_x\in\{0,1,2\}\) be the remaining number of cells to choose in column \(x\), and let \(n_x\) be the container size there. Put \(R=\sum_xr_x=h+d-t\). Weighted AM–GM gives
\[
 \prod_x n_x^{r_x}
 \le \left(\frac{\alpha h^2}{R}\right)^R
       \prod_xr_x^{r_x}
 \le4^d\left(\frac{\alpha h^2}{h+d-t}\right)^{h+d-t}.
\tag{1}
\]
We again overcount ordering and repeated cells.

Let \(N_{h,d,\pi}\) count independent sets with one or two selected cells per column and exactly \(d\) double columns. Then
\[
 N_{h,d,\pi}
 \le \binom hd4^d
 \sum_{t=0}^{s_h}\binom{h+d}{t}h^t
 \left(\frac{\alpha h^2}{h+d-t}\right)^{h+d-t}.
\tag{2}
\]
For large \(h\), the function
\[
 R\longmapsto(\alpha h/R)^R
\]
is decreasing on \(R\ge h-s_h\): its logarithmic derivative is \(\log(\alpha h/R)-1<0\). Thus the normalized factor in (2) is at most its value with \(d=0\). Also
\[
 \max_{t\le s_h}\binom{h+d}{t}
 \le\max_{t\le s_h}\binom{2h}{t}
 =\exp(o_\eta(h)),
\]
uniformly in \(0\le d\le h\). It follows that there is a number \(\varepsilon_h(\eta)\to0\), independent of \(d\) and \(\pi\), such that
\[
 \boxed{\displaystyle
 N_{h,d,\pi}
 \le \binom hd(4h)^d
       \bigl[(\alpha+\varepsilon_h(\eta))h\bigr]^h.}
\tag{3}
\]

The additional \(h^d\) pays for the extra selected cells. It does not multiply the principal sea factor once per ordinary column.

## 3. Assemble the full word

Write \(m=bh+r\), \(0\le r<h\). Split the first \(bh\) columns into full blocks. Summing their double counts uses Vandermonde's identity. The last \(r\) columns have at most
\[
 \binom r{d_r}h^{r+d_r}
\]
choices if they contain \(d_r\) doubles. There are fewer than \(2^h\) balanced partitions.

Consequently
\[
 E_h(m)\le
 2^h\binom m{q_h}(4h)^{q_h}
 \bigl[(\alpha+\varepsilon_h(\eta))h\bigr]^{m-r}h^r.
\tag{4}
\]
The harmless factor \(4^{d_r}\) has been added when combining the remainder with the full blocks.

If \(m/(h^2\log h)\to\infty\), then
\[
 \frac{h+\log\binom m{q_h}+q_h\log(4h)+O(h\log h)}m\to0.
\]
For the binomial term, put \(t=m/q_h\) and use
\[
 \frac1m\log\binom m{q_h}\le\frac{\log(et)}t.
\]
Taking \(m\)-th roots in (4), then \(h\to\infty\) and finally \(\eta\downarrow0\), proves
\[
 \limsup\frac{E_h(m)^{1/m}}h\le\frac12.
\tag{5}
\]
For \(a_h(m)\), require in addition that equality has been established at
the chosen widths. For every fixed \(\delta>0\), the sharper construction
guarantees this throughout \(m\gg_\delta h^2(\log h)^{2+\delta}\).
The weaker condition in (5) by itself does not guarantee equality.

## 4. A matching joint regime

Fix \(\delta>0\). The construction in
[safe_triangle_pair_first_moment.md](safe_triangle_pair_first_moment.md)
has a fixed completed block of length
\[
 T_h=O_\delta\bigl(h^2(1+\log h)^{2+\delta}\bigr)
\]
containing all parity doubles. Add constant-row collars and boundary switches, if necessary, so its two ends have row 1. Each collar has length at least the support memory \(L=2W_h\). This changes \(T_h\) by only \(O(h^2)\).

Append a buffered odd-row core using the construction from [dense_residue_entropy_capture.md](dense_residue_entropy_capture.md). The two buffers have total length \(O(h^2)\), and their boundary-event product is at least
\[
 \exp\bigl(-O_\epsilon(h^{3/2+\epsilon})\bigr)
\]
by the incident-pressure estimate \(O_\epsilon(h^{-1/2+\epsilon})\). All core-only events have total product cost at most \(\exp[-O_\epsilon(nh^{-1+\epsilon})]\) for a core of length \(n\), by the full odd-alphabet estimate. Thus, after choosing the total width to be \(m\),
\[
 a_h(m)\ge
 \left\lceil\frac h2\right\rceil^{m-O(T_h)}
 \exp\!\left[-O_\epsilon(mh^{-1+\epsilon})
             -O_\epsilon(h^{3/2+\epsilon})\right].
\tag{6}
\]
The fixed block, buffers, and core are joined through constant row-1 collars, so every forbidden support at a join lies within a previously valid piece. The full pair set stays the parity pair set.

For example, fix \(\epsilon=1/4\). If
\[
 \frac{m}{h^2(1+\log h)^{3+\delta}}\longrightarrow\infty,
\tag{7}
\]
the \(O(T_h)\) lost core positions in (6) cost \(o(m)\) after their \(\log h\) factor is included. Equations (4) and (6) give the genuine simultaneous limit
\[
 \boxed{\displaystyle
 \frac{a_h(m)^{1/m}}h\longrightarrow\frac12
 \quad\text{whenever }h\to\infty
 \text{ and }m/[h^2(1+\log h)^{3+\delta}]\to\infty.}
\tag{8}
\]

This does not require unique dominant components, a fixed-height limit in \(m\), or a product formula for all maximum blackouts. The logarithmic exponent in (7) comes from the current construction and the cost of reserving its columns; no optimal joint threshold is asserted.

## 5. An explicit logarithmic lower error

The four-logarithm estimate in
[mixed_four_logarithmic_lower_bound.md](mixed_four_logarithmic_lower_bound.md)
improves the core cost in (6). The mean per column of all odd-core bad events is
\(O((1+\log h)^4/h)\): the mixed and six-cell families have this order, and
hidden rectangles have smaller order. For each fixed \(\delta>0\),
the same local-lemma product used in Section 4 therefore gives constants
\(C_0(\delta),C_1(\delta)>0\) such that
\[
 \boxed{\displaystyle
 \log a_h(m)\ge m\log(h/2)
 -C_1\left(
       \frac{m(1+\log h)^4}{h}
       +h^2(1+\log h)^{3+\delta}
      \right)}
\tag{9}
\]
for all sufficiently large \(h\) and every
\(m\ge C_0h^2(1+\log h)^{2+\delta}\).

Indeed the reserved construction and buffers cost
\(O(T_h\log h)=O_\delta(h^2(1+\log h)^{3+\delta})\). Fixing
\(\epsilon=1/4\) in the boundary estimate gives an additional
\(O(h^{7/4})\) logarithmic cost, absorbed by that term. Every core-only event
uses the full odd alphabet, so its probability and its total mean have the
four-logarithm bound. The full dependency criterion remains valid because
the boundary and bulk incident pressures both tend to zero.

Equation (9) is an unconditional lower bound for the number of optimal
blackouts. It does not assert a matching additive error in the upper bound,
or change the joint regime in (8).

## 6. A fixed second-logarithm refinement

The independently checked construction in
[two_moment_threshold_refinement.md](two_moment_threshold_refinement.md)
has length
\[
T_h=O\!\left(h^2(1+\log h)^2
                   (1+\log\log(3h))^C\right)
\]
for an absolute \(C\). Substituting this length in the same argument
sharpens (8) to
\[
\frac{a_h(m)^{1/m}}h\longrightarrow\frac12
\quad\text{if}\quad
h\longrightarrow\infty,\qquad
\frac{m}{h^2(1+\log h)^3
                (1+\log\log(3h))^C}\longrightarrow\infty.
\]
Likewise the deterministic construction term in (9) becomes
\(O(h^2(1+\log h)^3(1+\log\log(3h))^C)\). This is a direct
substitution of the shorter completed block; no new counting hypothesis
is used.

