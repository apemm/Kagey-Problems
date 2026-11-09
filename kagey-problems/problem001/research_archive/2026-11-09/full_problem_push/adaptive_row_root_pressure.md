# Adaptive primitive directions for row-defect pressure

9 November 2026. An adaptive cutoff on primitive directions gives the exact penalty
\[
 \frac rh\log^2\frac hr
\]
throughout the small relative row-defect range. The cutoff avoids a maximum-divisor bound. Its finite-end loss is \(O(\sqrt{rh})\).

Let \((c_0,X)\) be a protected row/column pair, with row alphabets of size \(h/2+O(1)\). The reference may be the slightly unbalanced quadratic law. Let c be balanced and differ from \(c_0\) on E, with \(r=|E|\). Use normalized fixed-final-F partition functions.

**Claim.** There are absolute \(R_0,\delta_0,a,C>0\) such that, for sufficiently large h and
\[
 R_0\le r\le\delta_0h,
\]
\[
 Z_{c,X}(n)\le
 \exp[C h(1+\log h)^2]\,
 \rho_{c_0,X}(h)^n
 \exp\left[-a\frac rh\log^2\frac hr\,n\right].
\tag{1}
\]
At the exact partition-function level, before replacing \(Z_{c_0,X}(n)\) by its growth rate, the finite-end loss of the new rooted family is \(O(\sqrt{rh})\). The complete proof passed [independent review](adaptive_row_root_independent_audit.md).

## 1. The truncated family

Put \(q=r/h\) and
\[
 R=\lfloor q^{-1/2}\rfloor.
\]
Choose \(\delta_0\) small, so R is at least a large absolute constant. Since \(r\ge1\), \(R\le\sqrt h\).

For each changed completion \(W=(x,w)\) eligible under the old column phase, choose \(\epsilon=\pm1\) toward the farther row boundary. For each primitive pair \(1\le a,b\le R\), take
\[
 U=(4ka,4\epsilon kb),\qquad
 V=(-4\ell b,4\epsilon\ell a),
\tag{2}
\]
where
\[
 \frac{h}{100b}\le k\le\frac{h}{50b},
 \qquad
 \frac{h}{100a}\le\ell\le\frac{h}{50a}.
\tag{3}
\]
All four points fit in the strip: their total vertical displacement is at most \(4h/25\). The three black corners are \(W+U,W+V,W+U+V\), in three distinct columns. Their coordinate changes are divisible by four, so all corners obey the same protected law. The changed completion and unchanged black rows give a new singleton rival.

The primitive harmonic sum satisfies
\[
 \sum_{\substack{a,b\le R\\(a,b)=1}}\frac1{ab}
 \asymp \log^2R.
\tag{4}
\]
For example, expanding the coprimality indicator gives
\[
 \sum_{d\le R}\frac{\mu(d)}{d^2}H_{\lfloor R/d\rfloor}^2
 =\frac{\log^2R}{\zeta(2)}+O(\log R).
\]
Thus each root has \(\Theta(h^2\log^2R)\) shapes, with bounded geometric multiplicity.

For each other changed row, requiring a side endpoint to lie there fixes k or \(\ell\). Requiring the opposite corner to lie there fixes \(\ell\) once k is chosen. Summing over primitive directions bounds the total deletions by
\[
 C rh\sum_{a,b\le R}\left(\frac1a+\frac1b\right)
 \le C rhR\log R.
\tag{5}
\]
Its ratio to the original family is \(O(qR/\log R)=o(1)\) as \(q\to0\). A fixed positive fraction survives for \(q\le\delta_0\).

A nonconstant protected column law makes every changed row eligible in half the columns. For a constant law and balanced c, at least \((r-1)/2\ge r/3\) changed rows are eligible when \(r\ge3\). This also covers a reference with class sizes differing by two, since such a reference has nonconstant matched column laws.

## 2. Uniform conditional counts

Fix one black cell and one completion row. If the cell is a side endpoint, the row difference fixes kb or \(\ell a\). There are at most R possible divisors, and the other scale sums to \(O(h\log R)\). This gives \(O(hR\log R)\) choices.

If the cell is the opposite corner, its row gives
\[
 kb+\ell a=d.
\]
For each primitive a,b, this has \(O(h/(ab)+1)\) solutions in (3). Their sum is
\[
 O(h\log^2R+R^2)\le O(hR\log R).
\]
The cell column fixes the horizontal translation. Consequently, one prescribed black cell belongs to at most
\[
 C rhR\log R
\tag{6}
\]
retained events.

Two prescribed black cells and one completion row determine only constantly many tilted rectangles. The completion locus is a circle or one of constantly many lines perpendicular to the fixed black segment. A line can be horizontal only if the two fixed black cells share a column; genuine prescribed cells have distinct columns. Each prescribed row therefore meets the locus in \(O(1)\) points. Thus two fixed assignments belong to \(O(r)\) retained events.

Three black corners determine their completion. After deduplication, two distinct events cannot share all three assignments.

Each event has probability \(\Theta(h^{-3})\). The raw incident probability at one column, and the conditional compatible-neighbor sum after prescribing one event, are at most
\[
 C\left(qR\log R+q\right).
\tag{7}
\]
Since \(R\le q^{-1/2}\), this is \(O(\sqrt q\log(1/q))\). Choose \(\delta_0\) sufficiently small to meet the fixed unthinned local-lemma and conditional lower-probability thresholds.

The retained protected bulk has vanishing incident and conditional extension weight, as in the earlier exact row-pressure proof. Therefore the joint argument gives
\[
 \Pr(A\mid\text{avoid any earlier events})\ge\Pr(A)/2
\]
for every new rooted event. No Bernoulli thinning is needed.

## 3. Mean, ends, and exact comparison

The surviving event mean in a long interval is at least
\[
 a q\log^2R\,n-O(rR).
\tag{8}
\]
For the end term, a fixed direction contributes total span at most
\[
 C h^3\left(a^{-2}+b^{-2}\right)
\]
over its scales. Summing \(a,b\le R\) gives \(O(h^3R)\) per completion row. Event probabilities are \(O(h^{-3})\), so all r rows lose at most \(O(rR)\). Bounded phase-period corrections are smaller. Here \(rR\le\sqrt{rh}\).

Retain old bulk certificates whose whole row geometry avoids E. Under equal labeled class sizes, their joint law agrees in the two product spaces by the classwise alphabet bijection fixing unchanged rows. Restoring deleted old bulk costs
\[
 \exp[O_\varepsilon(rn h^{-2+\varepsilon})].
\]
When labeled class sizes differ by one, the dummy-letter comparison costs \(\exp(O(n/h))\). Choose the absolute \(R_0\) large enough to absorb this cost into (8), uniformly for \(R_0\le r\le\delta_0h\). The bulk restoration is smaller still.

It follows that
\[
 Z_{c,X}(n)\le
 Z_{c_0,X}(n)
 \exp\left[C\sqrt{rh}
       -a q\log^2(1/q)n\right].
\tag{9}
\]
The [span-weighted protected cut estimate](protected_crossing_bulk_weight.md) gives
\[
 Z_{c_0,X}(n)\le
 \exp[C h(1+\log h)^2]\rho_{c_0,X}(h)^n.
\]
This proves (1).

The claim is an exact fixed-phase comparison. It does not impose a fixed power-saving bound \(r\le h^{1-d}\), and it does not assert that an arbitrary phase profile has the same pressure.

## 4. Errors around one global phase

Let the actual column phase differ from X on \(S\subseteq[1,n]\). Retain roots only when their three black columns and completion column avoid S. Their lost mean is at most
\[
 C|S|qR\log R.
\]
Retain old bulk certificates only when their black columns avoid S, as well as their geometry avoiding E. Restoring the old bulk at S costs \(\exp(C|S|\Lambda^4/h)\), where \(\Lambda=1+\log h\). Alphabet cardinality changes at S cost only \(\exp(O(|S|/h))\).

Thus, uniformly over arbitrary S,
\[
 Z_{c,S}(n)\le C_h Z_{c_0,X}(n)
 \exp[-aP_h(r)n+C|S|],
\tag{10}
\]
where \(P_h(r)=(r/h)\log^2(h/r)\). The constant is absolute because \(qR\log R\) is bounded for \(q\le\delta_0\). No spacing or local-density condition on S is used.

Summing over \(|S|\le\sigma n+O_h(1)\) gives
\[
 \log\rho_{c,\le\sigma}
 \le\log\rho_{c_0,X}-aP_h(r)+H_2(\sigma)+C\sigma.
\tag{11}
\]
In particular, suitable absolute b gives strict subdominance when
\[
 \sigma\le b\,\frac{P_h(r)}{\log(e/P_h(r))}.
\tag{12}
\]
This is stronger than the uniform \(r/h\) comparison when \(r/h\to0\). It remains a neighborhood of one global protected phase.


