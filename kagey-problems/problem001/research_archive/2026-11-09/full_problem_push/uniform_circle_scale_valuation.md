# Uniform scale averages for the mixed circle count

9 November 2026. This note proves the scale-valuation hypothesis isolated
in [mixed_four_leading_ratio_reduction.md](mixed_four_leading_ratio_reduction.md),
on every polynomially long scale interval. It does not settle the
primitive-direction parity weights or the short-arc contribution.

Write \(r_2(n)=\#\{(x,y)\in\mathbb Z^2:x^2+y^2=n\}\).
Let \(N\) be a positive integer with \(r_2(N)>0\), and define
\[
F_N(K)=\sum_{k\le K}r_2(k^2N).
\]
For every fixed \(C,\delta>0\), uniformly for
\[
1\le N\le h^C,\qquad h^\delta\le K\le h^C,
\]
there is a positive coefficient \(A_N\) such that
\[
F_N(K)=A_N K\log K
 \left(1+O_C\!\left(\frac{1+\log\log(3h)}{\log K}\right)+o(1)\right).
\tag{1}
\]
The final \(o(1)\) is uniform in this range. Explicitly,
\[
A_N=\frac{r_2(N)}{\pi}
 \prod_{\substack{p^\nu\Vert N\\p\equiv1\pmod4}}
 \left(1-\frac{2\nu}{(\nu+1)(p+1)}\right).
\tag{2}
\]

Consequently, under the weight \(r_2(k^2N)\), the three categories
\(\nu_2(k)=0,1,\ge2\) have relative weights
\[
\frac12,\quad\frac14,\quad\frac14,
\tag{3}
\]
up to a uniform \(o(1)\) error on \(k\le K\) or on \(K<k\le2K\).
This also holds with a fixed nonnegative bounded-variation weight
on a compact interval of positive \(k/K\), with positive integral.

## 1. An elementary mean for the base scale function

Put \(R(k)=r_2(k^2)/4\). If \(\rho(d)\) counts roots of
\(-1\) modulo \(d\), then the prime-power formulas give
\[
R(k)=\sum_{\substack{d\mid k\\d\ {\rm odd}}}\rho(d).
\tag{4}
\]
For odd \(d\), \(4\rho(d)\) is the number of primitive lattice
representations of \(d\) as a sum of two squares. Thus
\[
\sum_{\substack{d\le X\\d\ {\rm odd}}}\rho(d)
=\frac14\#\{(a,b):(a,b)=1,\ a\not\equiv b\pmod2,\
                         a^2+b^2\le X\}.
\]
Möbius inversion over odd common divisors and the elementary disk
estimate in the two opposite-parity residue classes give
\[
\sum_{\substack{d\le X\\d\ {\rm odd}}}\rho(d)
 =\frac{X}{\pi}+O(\sqrt X\log(2X)).
\tag{5}
\]
Indeed the unrestricted opposite-parity disk count is
\(\pi X/2+O(\sqrt X+1)\), and
\[
\frac14\frac{\pi}{2}
\sum_{\substack{j\ge1\\j\ {\rm odd}}}\frac{\mu(j)}{j^2}
=\frac{\pi}{8}\frac{1}{\zeta(2)(1-2^{-2})}
=\frac1\pi.
\]
The Möbius tail and summed boundary errors have the stated size.

Apply Dirichlet's hyperbola identity to (4), splitting at
\(\sqrt K\), and use (5) and partial summation. This yields
\[
\sum_{k\le K}R(k)
=\frac1\pi K\log K+B K
 +O(K^{3/4}\log(2K))
\tag{6}
\]
for an absolute constant \(B\). To see the error directly, the
first hyperbola sum contributes
\(\sqrt K\log K\sum_{j\le\sqrt K}j^{-1/2}
 =O(K^{3/4}\log K)\).
The tail in the partial-summation constant has the same size
after multiplication by \(K\). No sharp circle estimate is needed.

## 2. A finite Euler correction for \(N\)

For each split prime \(p^\nu\Vert N\), let
\(c_p=2\nu/(\nu+1)\), so \(1\le c_p<2\).
Define the multiplicative function \(b_N\), supported on integers
whose prime factors divide the split part of \(N\), by
\[
b_N(1)=1,\qquad b_N(p^j)=(-1)^j c_p\quad(j\ge1).
\]
The local generating functions show exactly that
\[
\frac{r_2(k^2N)}{r_2(N)}=(R*b_N)(k).
\tag{7}
\]
For a split prime, its left local values are
\((\nu+2j+1)/(\nu+1)\). Dividing their generating function by
\(\sum_{j\ge0}(2j+1)x^j=(1+x)/(1-x)^2\) gives
\[
1-\frac{c_p x}{1+x}
=1+\sum_{j\ge1}(-1)^j c_p x^j.
\]
The prime two and inert primes need no correction.

For any fixed \(s>0\),
\[
\sum_{d\ge1}\frac{|b_N(d)|}{d^s}
=\prod_{\substack{p\mid N\\p\equiv1\pmod4}}
\left(1+\frac{c_p}{p^s-1}\right)
=N^{o(1)}.
\tag{8}
\]
The subpower estimate is uniform: for any \(\eta>0\), all
sufficiently large primes have their local factor at most \(p^\eta\);
the finitely many remaining primes contribute a fixed constant.

Put
\[
D_N(s)=\sum_{d\ge1}\frac{b_N(d)}{d^s}.
\]
Convolving (6) with \(b_N\), extending its main sums to infinity,
and using (8) at \(s=3/4\), gives
\[
F_N(K)=r_2(N)\left[
\frac{D_N(1)}{\pi}K\log K
+\left(BD_N(1)+\frac{D_N'(1)}{\pi}\right)K
+O_\eta\!\left(N^\eta K^{3/4}\log(2K)\right)
\right].
\tag{9}
\]
For the logarithmic tail one can use
\[
\sum_{d>K}\frac{|b_N(d)|\log(d/K)}d
\ll K^{-1/4}\sum_d\frac{|b_N(d)|}{d^{3/4}}.
\]
This proves the same error bound for the extended main terms.

The value \(D_N(1)\) is the product in (2). It is positive and
satisfies
\[
D_N(1)\ge \frac{c}{(1+\log\log(3N))^{C_0}},
\qquad
\left|\frac{D_N'(1)}{D_N(1)}\right|
\ll1+\log\log(3N).
\tag{10}
\]
These follow from the Euler factors and the elementary prime-sum
bounds \(\sum_{p\le Y}1/p\ll\log\log(3Y)\) and
\(\sum_{p\le Y}\log p/p\ll\log(3Y)\), splitting the prime
divisors of \(N\) at \(Y=\log(3N)\). For larger prime divisors,
use \(\sum_{p\mid N}\log p\le\log N\).

For \(N\le h^C\), \(K\ge h^\delta\), choose the fixed
\(\eta<\delta/(8C)\). The error in (9), divided by its main
term, tends to zero uniformly. Equation (10) controls the
linear term and proves (1).

## 3. The exact two-adic identities

The sum-of-two-squares formula gives
\[
r_2((2k)^2N)=r_2(k^2N)
\tag{11}
\]
for every \(k,N\). Hence, for each fixed \(j\ge0\),
\[
\sum_{\substack{k\le K\\\nu_2(k)=j}}r_2(k^2N)
 =F_N(K/2^j)-F_N(K/2^{j+1}).
\tag{12}
\]
Applying (1) gives
\[
\sum_{\substack{k\le K\\\nu_2(k)=j}}r_2(k^2N)
 =\left(2^{-j-1}+o(1)\right)A_NK\log K.
\]
Also
\[
\sum_{\substack{k\le K\\4\mid k}}r_2(k^2N)=F_N(K/4),
\]
which proves the third weight in (3) without summing infinitely
many individual valuation errors. Differences of partial sums
give the dyadic-interval version. Partial summation gives the
bounded-variation version on a fixed compact interval of positive
scaled \(k\)-values.

## 4. What this does and does not settle

The two-adic scale weights are therefore proved uniformly on the
polynomially long boxes used in the logarithmic bulk calculation.
The subsequent
[short-scale truncation](mixed_short_scale_truncation.md)
supplies the separate estimate needed to remove short scale boxes
from the complete leading vertical contribution.

The result does not prove equal primitive parity-type weights,
uniform connector residues, or negligible horizontal short arcs.
It therefore does not establish the candidate mixed ratios
\(13/16\) and \(5/4\), or an ordering of the full component
entropies.

