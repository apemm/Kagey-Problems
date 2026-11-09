# Primitive parity weights in the vertical range

9 November 2026. The three primitive direction types have equal leading weight in the nearly vertical range. The proof uses divisor pairing, an absolutely convergent correction, and parity cancellation on odd arithmetic progressions. It does not need an asymptotic theorem for divisor sums over thin quadratic-form regions.

Put \(\Lambda=\log(2h)\), and let \(0<\delta\le1\). For a primitive positive pair \((a,b)\), write \(N=a^2+b^2\), and use the scale coefficient from [uniform_circle_scale_valuation.md](uniform_circle_scale_valuation.md):
\[
 A_N=\frac4\pi\prod_{\substack{p^\nu\parallel N\\p\equiv1\ (4)}}
       \left(1+\nu\frac{p-1}{p+1}\right).
\tag{1}
\]
For \(T\in\{\mathrm{OO},\mathrm{OE},\mathrm{EO}\}\), define
\[
 W_T(h,\delta)=
 \sum_{\substack{1\le b\le h,\ 1\le a\le\delta b\\
                  (a,b)=1,\ (a,b)\text{ has type }T}}
 \frac{A_{a^2+b^2}}{ab}\log\frac hb.
\tag{2}
\]
The letters specify the parities of \(a,b\), in that order.

**Theorem.** Uniformly over choices \(0<\delta=\delta_h\le1\),
\[
 W_{\mathrm{OO}}-W_{\mathrm{OE}}=o(\Lambda^4),\qquad
 W_{\mathrm{OO}}-W_{\mathrm{EO}}=o(\Lambda^4).
\tag{3}
\]
For \(\delta_h=1/\log h\), each weight is \(\Theta(\Lambda^4)\). Consequently each type contributes \(1/3+o(1)\) of their total weight.

The theorem establishes the remaining primitive-type input in [mixed_four_leading_ratio_reduction.md](mixed_four_leading_ratio_reduction.md). It concerns the coefficient-weighted vertical sum. The separate angle, scale, connector, and base-residue arguments are still needed when applying it to geometric support counts.

## 1. A positive extension and a convergent correction

Suppress the common factor \(4/\pi\) during the proof. For every positive integer \(n\), define
\[
 B(n)=\prod_{p^\nu\parallel n,\ p\text{ odd}}(1+\nu\alpha_p),
 \qquad
 \alpha_p=
 \begin{cases}(p-1)/(p+1),&p\equiv1\pmod4,\\1,&p\equiv3\pmod4.
 \end{cases}
\tag{4}
\]
If the odd part of \(\gcd(a,b)\) is one, then \(a^2+b^2\) has no odd prime factor congruent to three modulo four. Thus \(B(a^2+b^2)=\pi A_{a^2+b^2}/4\), with \(A\) extended invariantly under multiplication of its argument by four.

Let \(q\) be multiplicative, supported on squarefree products of primes congruent to one modulo four, with
\[
 q(p)=-\frac2{p+1}.
\]
For the odd part \(n_o\) of \(n\), the exact convolution is
\[
 B(n)=\sum_{d\mid n_o}q(d)\tau(n_o/d).
\tag{5}
\]
Define its positive majorant
\[
 G(n)=\sum_{d\mid n_o}|q(d)|\tau(n_o/d).
\tag{6}
\]
At a split prime its local factor is \(1+\nu(1+2/(p+1))\). At an inert prime it is \(1+\nu\). In particular,
\[
 G(4n)=G(n),\qquad
 G(s^2n)\le\tau(s^2)^2G(n).
\tag{7}
\]
For the second inequality, each local coefficient is at most two, and
\(1+(\nu+2e)\alpha\le(1+\nu\alpha)(2e+1)^2\).

Let \(\rho(m)\) count the roots of \(-1\) modulo an odd positive integer \(m\), with \(\rho(1)=1\). The elementary bounds in the logarithmic-order note give
\[
 \sum_{m\le X}\rho(m)\ll X,\qquad
 \sum_{m\le X}\frac{\rho(m)}m\ll\log(2X),\qquad
 \rho(dm)\le\rho(d)\rho(m).
\tag{8}
\]
Moreover,
\[
 \sum_d\frac{|q(d)|\rho(d)}{\sqrt d}<\infty.
\tag{9}
\]
Its Euler factor at a split prime is \(1+4/((p+1)\sqrt p)\). The analogous sum with denominator \(d\) also converges.

## 2. Uniform bounds for the majorant

For \(1\le A\le B\), divisor pairing in (6) gives
\[
 \sum_{\substack{A\le a<2A,\ B\le b<2B\\(a,b)=1}}
 G(a^2+b^2)\ll AB\log(2B).
\tag{10}
\]
Indeed, each summand is at most
\[
 2\sum_d|q(d)|
 \sum_{\substack{m\le3B/\sqrt d\\dm\mid a^2+b^2}}1.
\]
Primitivity implies \((a,dm)=1\), so for fixed \(a,d,m\), the possible \(b\)'s occupy \(\rho(dm)\) residue classes modulo \(dm\). Their number is at most
\(C\rho(dm)(B/(dm)+1)\). Summing over \(m\) gives
\[
 C\rho(d)\left(\frac{B\log(2B)}d+\frac B{\sqrt d}\right).
\]
Equation (9), followed by the sum over \(a\), proves (10). Symmetry covers \(B<A\).

Dyadic summation and (7) imply
\[
 \sum_{1\le a,b\le h}\frac{G(a^2+b^2)}{ab}\ll\Lambda^3,
 \qquad
 \sum_{1\le a,b\le h}\frac{G(a^2+b^2)}{ab}\log\frac hb
 \ll\Lambda^4.
\tag{11}
\]
For the unrestricted sums, write \(a=sa_0,b=sb_0\) with \((a_0,b_0)=1\), and use
\(\sum_s\tau(s^2)^2/s^2<\infty\).

The same box proof allows the additional restriction \(2^T\mid a\), with \(b\) odd and \((a,b)=1\). There are at most \(C A/2^T\) available \(a\)'s in every nonempty dyadic interval. Therefore
\[
 \sum_{\substack{1\le b\le h,\ 1\le a\le\delta b\\
                   b\text{ odd},\ (a,b)=1,\ 2^T\mid a}}
 \frac{B(a^2+b^2)}{ab}\log\frac hb
 \ll 2^{-T}\Lambda^4.
\tag{12}
\]
The constant is independent of \(T,h,\delta\).

## 3. Remove the parity-sensitive hyperbola cutoff

Write \((a,b)_o=1\) when \(\gcd(a,b)\) is a power of two. Fix \(t\ge0\), and restrict to \(\nu_2(a)=t\). On this set,
\[
 \nu_2(a^2+b^2)\le2t+1.
\tag{13}
\]
Since \(a\le\delta b\le b\), for every odd \(d\mid a^2+b^2\),
\[
 \frac{b}{2^{t+1/2}\sqrt d}
 \le\sqrt{\frac{(a^2+b^2)_o}{d}}
 \le\frac{\sqrt2 b}{\sqrt d}.
\tag{14}
\]
Apply the exact divisor identity
\(\tau(n)=2\sum_{m\mid n,\ m\le\sqrt n}1-\mathbf1_{n\text{ square}}\)
inside (5). Replace the cutoff by \(b/\sqrt d\). The resulting expression is
\[
 \widetilde B(a,b)=
 2\sum_dq(d)
 \sum_{\substack{m\le b/\sqrt d\\dm\mid a^2+b^2\\(a,dm)=1}}1.
\tag{15}
\]
Both \(d,m\) are odd. The coprimality restriction in (15) is automatic when \((a,b)_o=1\). It is inserted before extending the sum to nonprimitive pairs.

Replacing \(B\) by \(\widetilde B\) in either parity of \(b\), with weight \(\log(h/b)/(ab)\), has total error
\[
 O_t(\Lambda^3).
\tag{16}
\]
To check this bound, every changed divisor, including the subtracted square term, lies in a fixed multiplicative band
\(b\asymp_t m\sqrt d\). Drop the odd-gcd restriction, retain \((a,dm)=1\), and count the \(b\)'s by their \(\rho(dm)\) residue classes. Their total weighted contribution, before the factor \(1/a\), is at most
\[
 C_t\Lambda\rho(dm)
       \left(\frac1{md}+\frac1{m\sqrt d}\right).
\]
Summing \(m\) costs one logarithm by (8). Summing \(a\) with weight \(1/a\) costs one more. Equation (9) completes the bound. This argument is uniform in \(0<\delta\le1\).

## 4. Odd and even second coordinates have equal weight

Define
\[
 \begin{aligned}
 O_t(h,\delta)&=
 \sum_{\substack{b\le h,\ a\le\delta b\\
                 \nu_2(a)=t,\ b\text{ odd},\ (a,b)_o=1}}
 \frac{B(a^2+b^2)}{ab}\log\frac hb,\\
 E_t(h,\delta)&=
 \sum_{\substack{b\le h,\ a\le\delta b\\
                 \nu_2(a)=t,\ b\text{ even},\ (a,b)_o=1}}
 \frac{B(a^2+b^2)}{ab}\log\frac hb.
 \end{aligned}
\tag{17}
\]
All coordinates are positive. For each fixed \(t\),
\[
 O_t(h,\delta)-E_t(h,\delta)=o_t(\Lambda^4),
\tag{18}
\]
uniformly in \(\delta\).

First replace \(B\) by (15), using (16). In the remaining sum, replace
\[
 \mathbf1_{(a,b)_o=1}
 =\sum_{\substack{r\mid a,b\\r\text{ odd}}}\mu(r)
\]
by the part with \(r\le D\), where \(D=\Lambda^2\). The discarded part has absolute weighted sum at most
\[
 C\Lambda^4\sum_{r>D}\frac{\tau(r^2)^2}{r^2}
 \ll \Lambda^4\frac{\log^8(2D)}D=o(\Lambda^4).
\tag{19}
\]
Indeed the absolute value of (15) is at most \(2G(a^2+b^2)\). For each common divisor \(r\), scale \(a,b\) by \(r\), and apply (7) and (11). The tail bound follows from \(\tau(r^2)^2\le d_9(r)\) and the elementary estimate \(\sum_{r\le X}d_9(r)\ll X\log^8(2X)\).

It remains to compare the two parities in the truncated sum. Fix \(a,r,d,m\), where \(r\mid a\). The condition \((a,dm)=1\) implies \((r,dm)=1\). Thus the divisibility conditions on \(b\) define \(\rho(dm)\) progressions modulo the odd modulus \(rdm\).

The allowed interval starts at
\[
 B_0=\max(a/\delta,m\sqrt d)
\]
and ends at \(h\). Along any progression of odd modulus, successive terms have alternating parity. The function \(\log(h/b)/b\) is nonnegative and decreasing for \(b\le h\). Hence its odd-even discrepancy is at most
\[
 C\rho(dm)\frac{\Lambda}{\max(a/\delta,m\sqrt d)}.
\tag{20}
\]
Splitting the \(m\)-sum at \(a/(\delta\sqrt d)\) and using (8) gives
\[
 \sum_{m\le h/\sqrt d}
 \frac{\rho(m)}{\max(a/\delta,m\sqrt d)}
 \ll\frac\Lambda{\sqrt d}.
\tag{21}
\]
After the convergent \(d\)-sum, (20) costs at most \(C\Lambda^2\) for each \(a,r\), before the factor \(1/a\). Finally,
\[
 \sum_{a\le h}\frac1a
      \sum_{\substack{r\le D\\r\mid a}}1
 \ll\Lambda\log(2D).
\tag{22}
\]
The parity discrepancy is therefore
\[
 O_t(\Lambda^3)+O(\Lambda^3\log(2D))
 +O\!\left(\Lambda^4\frac{\log^8(2D)}D\right)
 =o_t(\Lambda^4).
\tag{23}
\]
This proves (18).

## 5. Division by two balances the three primitive types

For \(t\ge1\), dividing both coordinates of the even-\(b\) sum by two gives the exact identity
\[
 E_t(h,\delta)=\frac14
       \bigl(O_{t-1}(h/2,\delta)+E_{t-1}(h/2,\delta)\bigr).
\tag{24}
\]
The parameter \(\delta\) stays unchanged. The factor \(1/4\) comes from \(1/(ab)\), and \(B(4N)=B(N)\).

For either parity sum, changing \(h\) to \(h/2\) while keeping \(\delta\) fixed costs \(O(\Lambda^3)\). Below \(h/2\), the logarithmic weights differ by \(\log2\). Above \(h/2\), the original logarithm is at most \(\log2\). Equation (11) bounds both contributions. Combining this observation with (18) and (24) gives, for every fixed \(t\),
\[
 O_t(h,\delta)=2^{-t}O_0(h,\delta)+o_t(\Lambda^4).
\tag{25}
\]

The primitive OO, OE, and EO sums, after suppressing \(4/\pi\), are respectively
\[
 O_0,\qquad E_0,\qquad\sum_{t\ge1}O_t.
\tag{26}
\]
Equation (18) with \(t=0\) compares the first two. For the third, fix an integer \(T\), apply (25) for \(1\le t<T\), and use (12) for \(t\ge T\). Thus
\[
 \limsup_{h\to\infty}
 \sup_{0<\delta\le1}
 \frac{|\sum_{t\ge1}O_t-O_0|}{\Lambda^4}
 \ll2^{-T}.
\]
Letting \(T\to\infty\) proves (3).

## 6. The vertical weight has four logarithms

The upper bound follows from (11). For the lower bound at \(\delta=1/\log h\), use odd primitive pairs in dyadic boxes with
\[
 h^{1/10}\le A\le h^{3/25},\qquad
 h^{4/25}\le B\le h^{9/50}.
\tag{27}
\]
For large \(h\), all these boxes satisfy \(a/b\le1/\log h\), and \(\log(h/b)\asymp\Lambda\). There are \(\gg\Lambda^2\) pairs of dyadic scales.

For completeness, the primitive congruence estimate (7) in [mixed_four_logarithmic_lower_bound.md](mixed_four_logarithmic_lower_bound.md) gives, uniformly for squarefree split-prime products \(d\le Y=h^{1/1000}\),
\[
 \#\{(a,b)\text{ odd primitive in the box}:d\mid a^2+b^2\}
 \gg AB\frac{\rho(d)}d\prod_{p\mid d}\frac p{p+1}.
\tag{28}
\]
The positive divisor expansion of (1), restricted to these \(d\), therefore shows
\[
 \sum_{\substack{(a,b)\text{ odd primitive}\\(a,b)\text{ in the box}}}
 B(a^2+b^2)
 \gg AB\sum_{\substack{d\le Y\\d\text{ squarefree on split primes}}}
 \frac1d\prod_{p\mid d}\frac{2p(p-1)}{(p+1)^2}
 \gg AB\log h.
\tag{29}
\]
For the last inequality, the prime weight is \(2/p+O(p^{-2})\) on primes congruent to one modulo four. The Mertens product and truncation argument already used in that note gives \(\gg\log Y\). Each box contributes \(\gg\Lambda^2\) to (2), and summing (27) proves \(W_{\mathrm{OO}}\gg\Lambda^4\). Equation (3) gives the same lower bound for OE and EO.

## 7. Scope of the conclusion

This proof supplies equality of the three leading primitive-type weights without computing their common absolute constant. Together with the established vertical geometric reduction, the uniform circle-scale estimate, and connector/base averaging, it permits the exact local phase table to be averaged over the vertical leading term. Any conclusion for the full mixed count must also use the separately proved negligible horizontal range and the short-scale truncation.

The proof does not compare a protected phase with an entire recurrent component. Such a comparison requires control of words outside the protected phase.
