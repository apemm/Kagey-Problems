# A square filter for mixed supports on one sea row

9 November 2026. The actual equal-norm condition saves one logarithm in the unrestricted count of the surviving mixed family with two label points and two points on the same sea row. This is a geometric counting lemma. It does not yet improve the complete-board width theorem.

Fix a sea row \(s\) and a label point at distance \(a>0\) from it. Assume the second label point is on the same side of that sea row, at distance at most \(h\). Count mixed supports whose oblique black side contains the fixed label point and one sea point, and whose black diagonal contains the other label point and another point on row \(s\). Both associated rectangles must be integral and nondegenerate. In the intended application all four required black columns are distinct, which already excludes a vertical black side.

Define
\[
 J(a)=\sum_{k\mid a}\sigma_{-1}(k)
     =\sum_{d\mid a}\frac{\tau(a/d)}d.
\tag{1}
\]
Then the number of such relative geometric configurations is
\[
 \boxed{O(hJ(a)).}
\tag{2}
\]
The bound ignores any additional modular or coloring restrictions, so it applies to every refined profile considered here. After summing the fixed endpoint row,
\[
 \sum_{a\le h}O(hJ(a))=O(h^2\log(2h)).
\tag{3}
\]
The previous divisor-only bound for this role was \(O(h\tau(a)\log h)\) per endpoint, with total \(O(h^2\log^2h)\).

The square filter and summation passed
[independent review](same_sea_square_filter_independent_audit.md).

## 1. Primitive side and connector coordinates

Translate the sea row to zero and, if needed, reflect vertically. Orient the side from its sea point to its label point. A horizontal reflection lets its vector be
\[
 U=k(p,q),\qquad p,q,k>0,\quad(p,q)=1,\quad kq=a.
\tag{4}
\]
The fixed endpoint determines its side's sea point once \(k,p\) are given. Thus \(k\mid a\), \(q=a/k\), and \(p\) is the only remaining side parameter.

The common white pair is an integral translate of this side, so its connector is
\[
 T=l(-q,p),\qquad l\in\mathbb Z\setminus\{0\}.
\tag{5}
\]
The black diagonal has the same midpoint as that common pair. Its sea endpoint has height zero. Therefore its other endpoint has height
\[
 c=a+2lp.
\tag{6}
\]
In particular, \(|lp|\le h\). The factor two and the stronger strip bound are unnecessary for the upper estimate.

Writing \(v\) for the horizontal component of the black diagonal, equality of lengths gives
\[
 v^2=k^2(p^2+q^2)-c^2
     =p^2(k^2-4l^2)-4lpkq.
\tag{7}
\]
For fixed \(k,p,l\), at most two choices of \(v\) remain. They determine the second label point and second sea point, up to a bounded choice of endpoint orientation. Thus it is enough to count triples \((k,p,l)\) satisfying the necessary square condition in (7).

## 2. The odd squarefree part must divide the connector scale

Let
\[
 u(p)=\prod_{\substack{\ell\text{ odd prime}\\\nu_\ell(p)\text{ odd}}}\ell.
\]
Equation (7) implies
\[
 u(p)\mid lk.
\tag{8}
\]
Indeed, suppose \(\ell^e\parallel p\), where \(\ell\) is odd and \(e\) is odd. If \(\ell\nmid lk\), then \(\ell\nmid q\) by \((p,q)=1\). The term \(-4lpkq\) has valuation exactly \(e\), while the other term in (7) has valuation at least \(2e\). Their sum has odd valuation \(e\), contradicting that it is a square.

Since \(u(p)\) is squarefree, (8) requires \(l\) to be a multiple of
\(u(p)/\gcd(u(p),k)\). The number of nonzero such integers satisfying \(|lp|\le h\) is at most
\[
 \frac{2h\gcd(u(p),k)}{p\,u(p)}.
\tag{9}
\]
There is no additive counting error in this inequality: it bounds a symmetric interval of nonzero multiples by its length divided by the spacing.

## 3. The remaining sum converges

Write uniquely
\[
 p=2^euv^2,
\]
where \(e\ge0\), \(u\) is odd and squarefree, and \(v\) is odd. Then \(u=u(p)\), and
\[
 \begin{aligned}
 \sum_{p\ge1}\frac{\gcd(u(p),k)}{p\,u(p)}
 &=\sum_{e\ge0}2^{-e}
   \sum_{v\text{ odd}}v^{-2}
   \sum_{u\text{ odd squarefree}}\frac{\gcd(u,k)}{u^2}\\
 &\ll\prod_{\ell\mid k,\ \ell\text{ odd}}
          \frac{1+1/\ell}{1+1/\ell^2}
 \le C\sigma_{-1}(k).
 \end{aligned}
\tag{10}
\]
The universal Euler factor \(\prod_{\ell\text{ odd}}(1+1/\ell^2)\) is absorbed in the constant. Dropping \((p,q)=1\) after deriving the necessary condition only enlarges the count.

Sum (9) over \(p\) using (10), then over \(k\mid a\). This proves (2). Finally,
\[
 \sum_{a\le h}J(a)
 =\sum_{d\le h}\frac1d\sum_{m\le h/d}\tau(m)
 \ll h\log(2h)\sum_{d\ge1}d^{-2}
 \ll h\log(2h),
\]
proving (3).

## 4. Other pair roles and the limitation

This lemma treats the crossed pairing, where each black pair contains one label point and one sea point. It does not count a horizontal sea side with a label diagonal. In a completely occupied two-phase region, that horizontal role is excluded separately by [seven_phase_filler_profiles.md](seven_phase_filler_profiles.md).

If instead the labels form the black side and the two same-row sea points form its horizontal black diagonal, the common white pair is centered on the sea row. For a sea row within a bounded distance of a strip boundary, its vertical difference must be bounded. Hence the two label heights differ by \(O(1)\), and the norm equation factors a bounded nonzero square. This gives only \(O(1)\) possibilities per endpoint. Equal label heights make the diagonal rectangle degenerate.

For arbitrary sea points on rows separated by a nonzero integer \(d\), the counterpart of (7) contains the extra term \(4d(a-d)\). Odd primes dividing \(p\) then impose a quadratic-residue condition on that nonzero quantity, rather than the divisibility (8). The convergent sum (10) therefore does not apply unchanged. In the specific period-49 profile, however, [refined_filler_mixed_rigidity.md](refined_filler_mixed_rigidity.md) proves that a two-label/two-filler mixed support must use equal actual filler rows. Those filler pairs do fall under this lemma. Mixed pairs using the two different binary boundary levels remain separate.

Unused partner rows of the two labels, restrictions to arithmetic weight classes, higher-arity events, and the complete occupation/order requirement also remain in the placement problem. The theorem saves one logarithm in the actual same-row geometric family. A reduction of the final construction threshold would need estimates covering those remaining roles.
