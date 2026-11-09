# Averaged circle angles and horizontal mixed supports

9 November 2026. This note proves that the nearly horizontal contribution
in [mixed_four_leading_ratio_reduction.md](mixed_four_leading_ratio_reduction.md)
is lower order. The argument averages over the scale \(k\), rather than
claiming angular equidistribution on every individual circle.

Write \(\Lambda=1+\log h\) and
\[
r_2(n)=\#\{(x,y)\in\mathbb Z^2:x^2+y^2=n\}.
\]

## 1. A uniform mean angular estimate

For \(j\ne0\), define
\[
\lambda_{4j}(n)=\frac14
 \sum_{x^2+y^2=n}\exp(4ij\arg(x+iy)).
\]
For every fixed \(j\ne0\), there are absolute \(C,c>0\) such that
\[
\sum_{k\le K}|\lambda_{4j}(k^2N)|
 \ll_j r_2(N)K(\log(2K))^{2/\pi}
               (1+\log\log(3N))^C
\tag{1}
\]
whenever \(r_2(N)>0\). The exponent \(2/\pi<1\) is sufficient here;
no optimal angular exponent is asserted.

The normalized coefficients are multiplicative, by factorization
in the Gaussian integers. At a split prime \(p\), choose a Gaussian
prime of argument \(\theta_p\). Its local coefficient at exponent \(e\) is
\[
S_e(4j\theta_p)
 =\sum_{r=0}^e \exp\bigl(4ij(e-2r)\theta_p\bigr).
\]
At inert primes with even exponent and at two, the local coefficient
has absolute value one.

Let \(g=g_{j,N}\) be the nonnegative multiplicative function with
\[
g(p^e)=
\begin{cases}
|S_{2e}(4j\theta_p)|,&p\equiv1\pmod4,\ p\nmid N,\\
2e+1,&p\equiv1\pmod4,\ p\mid N,\\
1,&p=2\text{ or }p\equiv3\pmod4.
\end{cases}
\]
Then
\[
|\lambda_{4j}(k^2N)|\le \frac{r_2(N)}4g(k).
\tag{2}
\]
For \(p^\nu\Vert N\), this follows from
\(\nu+2e+1\le(\nu+1)(2e+1)\).
In particular, it does not divide by a possibly zero angular
coefficient of \(N\).

Uniformly in \(j,N\), \(g(p^e)\le2e+1\le3^e\) and
\(g(n)\le d_3(n)\ll_c n^c\) for every fixed \(c>0\).
Shiu's mean-value upper bound therefore gives, first on dyadic
intervals and then on \(k\le K\),
\[
\sum_{k\le K}g(k)
 \ll K\exp\left(\sum_{p\le2K}\frac{g(p)-1}{p}\right).
\tag{3}
\]
The constants in this application are independent of \(j,N\).
One precise statement is Lemma 2.18 of
[Matomäki, Radziwiłł, Shao, Tao and Teräväinen](https://link.springer.com/article/10.1007/s00222-026-01408-6);
the original result is
[Shiu, Theorem 1](https://doi.org/10.1515/CRLL.1980.313.161).
We use its \(q=1\), full-interval case.

For split primes not dividing \(N\),
\[
g(p)=|1+2\cos(8j\theta_p)|
 \le1+2|\cos(8j\theta_p)|.
\]
The Gaussian-prime angular estimate in Theorem 5 of
[Fainsilber, Kurlberg and Wennberg](https://kurlberg.github.io/eprints/circle2.pdf)
gives, for fixed \(j\ne0\),
\[
\sum_{\substack{p\le X\\p\equiv1\pmod4}}
 \frac{|\cos(8j\theta_p)|}{p}
 \le\frac1\pi\log\log X+O_j(1).
\tag{4}
\]
The finitely many small \(X\) can be absorbed in the \(j\)-dependent
constant. At split primes dividing \(N\), replacing the angular
local factor by three costs at most \(3/p\). Consequently
\[
\sum_{p\le X}\frac{g(p)-1}{p}
 \le\frac2\pi\log\log(3X)
       +3\sum_{p\mid N}\frac1p+O_j(1).
\]
Splitting the prime divisors of \(N\) at \(\log(3N)\) proves
\[
\exp\left(3\sum_{p\mid N}\frac1p\right)
 \ll (1+\log\log(3N))^C.
\]
Together with (2)--(3), this proves (1).

The use of Shiu's theorem matters: the weaker mean-value theorem
stated in the circle paper assumes an \(O(K)\) unweighted mean,
which need not hold for our function \(g\).

## 2. Fixed arcs on polynomially long scale intervals

Let \(I\) be any fixed finite union of angular intervals. For fixed
\(C_0,\delta>0\), uniformly for \(N\le h^{C_0}\) with \(r_2(N)>0\)
and \(h^\delta\le K\le h^{C_0}\), we have
\[
\sum_{K<k\le2K}\#\{V\in\mathbb Z^2:
 |V|^2=k^2N,\ \arg V\in I\}
 =
 \left(\frac{|I|}{2\pi}+o(1)\right)
 \sum_{K<k\le2K}r_2(k^2N).
\tag{5}
\]
The \(o(1)\) is uniform in \(N,K\), for fixed \(I,C_0,\delta\).

Indeed the constant Fourier coefficient has size
\(A_NK\log K\), where
[uniform_circle_scale_valuation.md](uniform_circle_scale_valuation.md)
proves
\[
A_N\gg r_2(N)(1+\log\log(3N))^{-C}.
\]
All Fourier coefficients whose index is not divisible by four
vanish by rotational symmetry. For each fixed nonzero remaining
index, (1), divided by the constant coefficient, is
\[
O_j\left(
(\log K)^{2/\pi-1}(1+\log\log(3N))^{C'}
\right)=o(1).
\]
Apply finite trigonometric upper and lower approximations to
\(1_I\), with error at most \(O(1/M)\) in their integrals.
First fix \(M\), then let \(h\to\infty\), and finally let
\(M\to\infty\). This proves (5). Equivalently one can apply
the usual finite Fourier discrepancy inequality to the aggregate
positive measure of all these circles.

We do not need uniformity for shrinking arcs. In the next step the
arc width is held fixed until after the height tends to infinity.

## 3. The horizontal contribution is negligible

Let \(N_{\rm hor}(h)\) count the mixed geometries, per horizontal
translation, whose primitive common-side direction satisfies
\[
a/b>\log h,\qquad a,b>0,\quad(a,b)=1.
\]
Signs and reflections change only absolute constants. Then
\[
N_{\rm hor}(h)=o(h^3\log^4h).
\tag{6}
\]

Fix \(0<\varepsilon<1/4\) and \(0<\delta<1/2\).
Discard \(k\le h^\delta\). By
[mixed_short_scale_truncation.md](mixed_short_scale_truncation.md)
this costs at most
\[
C h^3\Lambda^3+C\delta^2h^3\Lambda^4.
\tag{7}
\]

First consider \(k\le h/(\varepsilon a)\).
Bounding all circle representations, all connectors by \(Ch/a\),
and all base positions by \(h\), its contribution is at most
\[
C h^2\sum_{\substack{a/b>\log h\\(a,b)=1}}
 \frac{r_2(a^2+b^2)}a\,
 \frac{h}{\varepsilon a}\log(2h/(\varepsilon a)).
\tag{8}
\]
Terms with \(h/(\varepsilon a)<1\) are empty.
For fixed \(\varepsilon\) and sufficiently large \(h\),
the logarithm is \(O_\varepsilon(\Lambda)\).
The uniform primitive-box estimate
\[
\sum_{\substack{a\asymp A,\ b\asymp B\\(a,b)=1}}
 r_2(a^2+b^2)\ll AB\log(2\max(A,B))
\]
bounds the dyadic-box contribution in (8) by
\[
O_\varepsilon(h^3(B/A)\Lambda^2).
\]
There are \(O(\Lambda)\) possible \(A\)-scales, and for each
the sum of \(B/A\) over \(B\ll A/\log h\) is \(O(1/\log h)\).
Thus (8) is \(O_\varepsilon(h^3\Lambda^2)\).

For all remaining scales, \(ka>h/\varepsilon\).
Both black endpoints \((U\pm V)/2\) lie in the height-\(h\) strip,
so \(|V_y|<h\). Since \(|V|=k\sqrt{a^2+b^2}\ge ka\),
every allowable \(V\) lies in the fixed arc set
\[
I_\varepsilon=\{\theta:|\sin\theta|\le\varepsilon\},
\qquad |I_\varepsilon|=O(\varepsilon).
\]
Partition \(h^\delta<k\le h/b\) into dyadic intervals.
Any interval intersecting the actual remaining range can be
bounded by its full dyadic interval with the arc restriction;
the bounded overlap costs a fixed factor. Equation (5) then bounds
the circle count by \(O(\varepsilon)+o(1)\) times its full-circle
majorant, uniformly in the direction and the scale interval.
The total full-circle geometric majorant is
\(O(h^3\Lambda^4)\). Therefore
\[
\limsup_{h\to\infty}\frac{N_{\rm hor}(h)}{h^3\log^4h}
 \le C\delta^2+C\varepsilon.
\]
Let \(\delta\downarrow0\) and then \(\varepsilon\downarrow0\).
This proves (6).

The result concerns uncolored geometries, so it also bounds every
protected color subfamily. Together with the earlier balanced-direction
bound and vertical span replacement, it removes the angular obstruction
to the candidate mixed ratios. Equal leading weights of the three
primitive parity types are still needed.

