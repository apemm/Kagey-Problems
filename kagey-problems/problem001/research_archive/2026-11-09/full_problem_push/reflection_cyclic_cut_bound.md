# A linear reflection-cut bound on an even cyclic group

9 November 2026. The linear stability inequality has a self-contained Fourier proof on an even cyclic group. It transfers uniformly to integer intervals containing at least eight periods of a balanced periodic row coloring. The Fourier argument and the transfer have passed independent review. The general nonperiodic interval inequality was subsequently proved by a different argument in [Interval reflection stability](reflection_interval_stability.md).

Let \(N=2n\), let \(A\subseteq\mathbb Z/N\mathbb Z\) have size n, and put
\[
 e=|A\cap2\mathbb Z|,\qquad o=|A\setminus2\mathbb Z|.
\]
Define the cyclic reflection violation count by
\[
 V_{\mathrm{cyc}}(A)=
 \#\{(a,b)\in A^2:2a-b\notin A\},
\tag{1}
\]
with all arithmetic modulo N.

**Theorem.**
\[
 V_{\mathrm{cyc}}(A)\ge\frac12 eo.
\tag{2}
\]

The factor one half is only a convenient universal constant. No sharpness claim is made.

## 1. Fourier expansion of the violation count

Put \(g=2\,1_A-1\). It is a real-valued sign function with mean zero. Use normalized Fourier coefficients
\[
 \widehat g(r)=\frac1N\sum_{x\bmod N}g(x)e^{-2\pi irx/N}.
\]
Write
\[
 p=\widehat g(N/2),\qquad q=|p|,\qquad E=1-p^2.
\]
The coefficient p is real. Parseval gives
\[
 E=\sum_{r\notin\{0,N/2\}}|\widehat g(r)|^2.
\tag{3}
\]

Let
\[
 T=\mathbb E_{a,b\bmod N}g(a)g(b)g(2a-b)
   =\sum_r\widehat g(r)^2\widehat g(-2r).
\tag{4}
\]
Expanding the three factors in
\[
 1_A(a)1_A(b)(1-1_A(2a-b))
\]
gives
\[
 \frac{V_{\mathrm{cyc}}(A)}{N^2}
   =\frac{1-p^2-T}{8}
   =\frac{E-T}{8}.
\tag{5}
\]
All linear terms vanish. Of the pair correlations, only
\(\mathbb E\,g(b)g(2a-b)\) can be nonzero. Its Fourier modes satisfy \(2r=0\), so it equals \(p^2\), since the zero mode vanishes.

## 2. Bound the cubic correlation away from the parity energy

For every frequency r that is not its own negative,
\[
 |\widehat g(r)|\le1/\sqrt2.
\tag{6}
\]
Indeed its conjugate frequency has the same squared magnitude, and the two terms are bounded by the Parseval sum one.

The modes \(r=0,N/2\) make no contribution to (4), because \(\widehat g(0)=0\). For all remaining r, the factor \(\widehat g(-2r)\) obeys (6), except possibly when \(2r=N/2\). These exceptional modes exist only when \(4\mid N\), and are \(r=N/4,3N/4\). Let
\[
 E_4=|\widehat g(N/4)|^2+|\widehat g(3N/4)|^2
\]
when they exist, and let \(E_4=0\) otherwise.

Besides \(E_4\le E\), the sign-function property gives
\[
 E_4\le2(1-q)^2.
\tag{7}
\]
To see this, choose \(\sigma\in\{-1,1\}\) with \(\sigma p=q\). The sign functions g and \(\sigma(-1)^x\) disagree on a fraction \((1-q)/2\) of the group, so
\[
 \mathbb E|g(x)-\sigma(-1)^x|=1-q.
\]
At either order-four frequency the subtracted parity character has zero Fourier coefficient. Thus each corresponding coefficient of g has magnitude at most \(1-q\).

Set \(a=1/\sqrt2\). Equations (3)--(7) give
\[
 T\le a(E-E_4)+qE_4.
\tag{8}
\]
If \(q\le a\), then \(T\le aE\le3E/4\). If \(a<q<1\), then
\[
 \begin{aligned}
 \frac TE
 &\le a+\frac{2(q-a)(1-q)}{1+q}\\
 &\le a+\frac{(1-a)^2}{2(1+a)}
   =\frac{5}{4(1+a)}
   <\frac34.
 \end{aligned}
\tag{9}
\]
The second line uses \((q-a)(1-q)\le(1-a)^2/4\) and \(1+q\ge1+a\). The final inequality follows from \(a>2/3\). If \(q=1\), then g is a parity character up to sign, and \(E=T=0\).

Therefore
\[
 T\le\frac34E
\]
in all cases. Equation (5) yields \(V_{\mathrm{cyc}}\ge N^2E/32\). Finally,
\[
 p=\frac{e-o}{n},\qquad
 E=1-\frac{(e-o)^2}{n^2}=\frac{4eo}{n^2}
   =\frac{16eo}{N^2},
\]
which proves (2).

## 3. Transfer to a balanced periodic row coloring

Let a coloring of the integer line have an even period N, with exactly \(N/2\) rows of each color per period. Let A be one color in the prefix \([1,h]\), and let \(V_h(A)\) count only reflections whose two endpoints remain inside that prefix.

If \(h=HN\) with \(H\ge8\), then
\[
 V_h(A)\ge \frac1{32}|A\cap2\mathbb Z|\,
                         |A\setminus2\mathbb Z|.
\tag{10}
\]
Take centers
\[
 \lfloor h/4\rfloor+1\le a\le h-\lfloor h/4\rfloor
\]
and steps \(1\le k\le\lfloor h/4\rfloor\). All endpoints stay inside the interval. Every center residue modulo N occurs at least \(H/4\) times in this range, and every step residue occurs at least \(H/8\) times. Thus
\[
 V_h(A)\ge \frac{H^2}{32}
 \sum_{a,k\bmod N}
       1_A(a)\,1_{\{c(a-k)\ne c(a+k)\}}.
\]
The sum is \(2V_{\mathrm{cyc}}\): for each cyclic center, k and \(-k\) give the two orientations of a mismatching endpoint pair. Hence
\[
 V_h(A)\ge \frac{H^2}{16}V_{\mathrm{cyc}}
       \ge\frac{H^2}{32}eo,
\]
where e and o are the parity counts in one period. The prefix counts are He and Ho, proving (10).

For arbitrary \(h\ge8N\), trim to \(H=\lfloor h/N\rfloor\) full periods. Each parity count in the longer prefix is at most \((H+1)\) times its one-period count. Since \(H\ge8\), the same argument gives the convenient uniform bound
\[
 V_h(A)\ge \frac1{64}|A\cap2\mathbb Z|\,
                         |A\setminus2\mathbb Z|.
\tag{11}
\]
In particular, \(V_h(A)\le Mh\) forces this balanced periodic coloring to differ from a single ordinary parity coloring in \(O(M)\) rows, uniformly in N as long as \(N\le h/8\).

Here the incomplete final period causes no additive boundary error. Put \(b=\min(e,o)\). The better parity coloring differs from the given coloring at exactly \(2b\) places per full period, and therefore at at most \(2(H+1)b\) places in the prefix. Also \(eo\ge Nb/4\). The lower bound before (11) gives
\[
 V_h(A)\ge H^2Nb/128.
\]
Since \(h<(H+1)N\) and \(H\ge8\), the distance is at most \(324\,V_h(A)/h\), and hence at most \(324M\).

The Fourier theorem controls cyclic reflections, while the original strip condition ignores reflections leaving the row interval. Simply periodizing an arbitrary row word can introduce many additional violations. No bound on those introduced violations is proved here, so (2) is not being used to assert the general interval inequality.

