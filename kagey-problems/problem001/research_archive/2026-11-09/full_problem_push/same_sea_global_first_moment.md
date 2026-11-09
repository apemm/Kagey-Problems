# The same-sea mixed family has quadratic global incidence

9 November 2026. The in-strip norm inequality strengthens [same_sea_mixed_square_filter.md](same_sea_mixed_square_filter.md). For a sea row at a bounded distance from a strip boundary, the total geometric incidence over both selected label rows is \(O(h^2)\), with no logarithmic factor.

This is a global first-moment result for that family. It does not give a uniform bound for an endpoint in the black-diagonal role or a complete label-placement theorem.

The subsequent [uniform square-compatibility argument](same_sea_mixed_power_saving.md)
strengthens the fixed-side bound to \(O_\varepsilon(h^{1/2+\varepsilon})\)
and the global count to \(O_\varepsilon(h^{3/2+\varepsilon})\).

## 1. The additional scale bound

Translate the sea row to zero and reflect vertically when the sea is near the upper boundary. The two label points lie on the positive side. Let the fixed label point in the black side be at row \(a>0\). Retain the notation
\[
 U=k(p,q),\quad kq=a,\quad (p,q)=1,\qquad
 T=l(-q,p),\qquad c=a+2lp.
\]
The side is oblique and the four black columns are distinct.

For \(l>0\), the equal-norm condition is
\[
 v^2=k^2p^2-4lp(a+lp).
\tag{1}
\]
Since the final term is positive, every genuine instance has
\[
 l<k/2,
\tag{2}
\]
in addition to \(lp\le h\). Write \(u(p)\) for the odd squarefree part of \(p\). The valuation proof in the preceding note gives \(u(p)\mid lk\). Thus the number of possible positive \(l\)'s for fixed \(p,k\) is at most
\[
 \min(k,h/p)\frac{\gcd(u(p),k)}{u(p)}.
\tag{3}
\]
As before, this count has no additive error because it counts nonzero multiples starting at the origin.

## 2. Sum the two scale restrictions together

Put
\[
 F_k(X)=\sum_{p\le X}\frac{\gcd(u(p),k)}{u(p)}.
\]
The unique decomposition \(p=2^euv^2\), with \(u\) odd and squarefree and \(v\) odd, gives
\[
 \begin{aligned}
 F_k(X)
 &\ll\sqrt X
   \sum_{u\text{ odd squarefree}}\frac{\gcd(u,k)}{u^{3/2}}\\
 &\ll\sqrt X\,\sigma_{-1/2}(k).
 \end{aligned}
\tag{4}
\]
Indeed the count of \((e,v)\) with \(2^ev^2\le X/u\) is \(O(\sqrt{X/u})\). The remaining Euler product has local factor \(1+p^{-3/2}\) away from primes dividing \(k\), and \(1+p^{-1/2}\) at those primes. Its convergent universal part is absorbed into the constant.

Partial summation gives
\[
 \sum_{p>X}\frac{\gcd(u(p),k)}{p\,u(p)}
 \ll X^{-1/2}\sigma_{-1/2}(k).
\tag{5}
\]
Split (3) at \(X=h/k\), which is at least one since \(k\mid a\le h\). Equations (4)–(5) imply
\[
 \sum_{p\ge1}\min(k,h/p)
               \frac{\gcd(u(p),k)}{u(p)}
 \ll\sqrt{kh}\,\sigma_{-1/2}(k).
\tag{6}
\]
Each \((k,p,l)\) determines at most a bounded number of geometries. Summing over \(k\mid a\) yields
\[
 \begin{aligned}
 I_{\mathrm{side}}(a)
 &\ll\sqrt h\sum_{k\mid a}\sqrt k\,\sigma_{-1/2}(k)\\
 &\le\sqrt{ah}\,\sigma_{-1/2}(a)^2.
 \end{aligned}
\tag{7}
\]
The last inequality uses monotonicity under divisibility and
\(\sum_{k\mid a}\sqrt k=\sqrt a\,\sigma_{-1/2}(a)\).

## 3. Boundary margins and bounded moments

If the sea row is at distance at most a fixed \(M\) from the boundary, a negative connector scale is possible only when \(|lp|\le M\). There are \(O_M(1)\) such pairs \((l,p)\), and at most \(\tau(a)\) choices of \(k\). This contributes \(O_M(\tau(a))\), which is absorbed by \(O_M(h)\). The same argument applies after reflection at the upper boundary.

For every fixed \(r>0\),
\[
 \sum_{a\le h}\sigma_{-1/2}(a)^r=O_r(h).
\tag{8}
\]
Here is an elementary proof. The function \(f(a)=\sigma_{-1/2}(a)^r\) is multiplicative, and its convolution \(g=f*\mu\) has nonnegative prime-power values. Its local series at exponent one is
\[
 \sum_{j\ge0}\frac{g(p^j)}{p^j}
 =(1-p^{-1})\sum_{j\ge0}\frac{f(p^j)}{p^j}
 =1+O_r(p^{-3/2}).
\]
Thus \(\sum_dg(d)/d<\infty\), and
\(\sum_{a\le h}f(a)=\sum_dg(d)\lfloor h/d\rfloor\ll_r h\).

Combining (7) with (8) at \(r=2\), and including the bounded-margin cases, proves
\[
 \boxed{\displaystyle
 \sum_{a\le h} I_{\mathrm{side}}(a)=O_M(h^2).}
\tag{9}
\]
The arithmetic weight \(\sigma_{-1/2}(a)^2\) in the fixed-side bound has bounded mean of every fixed positive power.

## 4. What remains for placement

The theorem applies to the low and high binary sea levels and to each of the seven bounded filler rows. The [refined filler rigidity theorem](refined_filler_mixed_rigidity.md) ensures that a two-label/two-filler mixed support uses one actual filler row, so it falls within this family.

The bound is asymmetric: it fixes the endpoint in the black side. Its global sum bounds the average degree in the diagonal role but does not, by itself, bound every such degree or every restricted arithmetic class. Assigning unused partners to the label endpoints introduces further factors. Full occupation, vertical parity rivals, other pair roles, and higher-arity constraints remain in the construction problem. No improved threshold is inferred from (9) alone.
