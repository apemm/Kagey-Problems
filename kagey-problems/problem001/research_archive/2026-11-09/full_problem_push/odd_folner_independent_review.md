# Independent review of the odd-input recurrence proof

9 November 2026. I checked `odd_graph_odd_folner_adaptation.md` against the stated analytic inputs and audited its character averaging, normalization, limits, and correspondence argument. The revised proof is valid. In particular, it proves unbounded chromatic number for the graph on positive odd integers with edges
\[
 u^2+4(v-u)^2=z^2.
\]
The conclusion is stronger than an obstruction to periodic or multiplicative colorings.

## 1. The source hypotheses

The relevant primary source is Frantzikinakis--Klurman--Moreira, [Partition regularity of generalized Pythagorean pairs](https://arxiv.org/html/2407.08360v2), Theorem 3.1, Propositions 4.7 and 4.9, and Lemma 6.3.

The quadratic form \(D(a,b)=-a^2+4ab+b^2\) has nonsquare discriminant 20. The linear factors \(a,b\) are independent. The modulus \(2^{K+1}Q\) belongs to the source's full small-prime family. Its quotient by the normalization factor 4 contains every required small prime and the fixed conductor for all sufficiently large \(K\). The varying residue bound is allowed to grow with \(K\). These hypotheses match the source statements.

## 2. A sign issue found and repaired

The residue value \(D(Q,1)/4\) is negative for large \(Q\). Applying an evenly extended pretentious function directly and then silently treating an odd Dirichlet character as periodic on negative inputs creates a sign ambiguity.

The revised proof avoids it. On positive integers define
\[
 g(n)=f(n)\overline{\chi(n)}n^{-it},
\]
extend \(g\) evenly, and apply quadratic concentration to \(g\) with comparison character 1 and twist zero. Zeros at conductor primes are allowed. The prime tail is exactly the original pretentious tail, once those finitely many primes are excluded.

On the positive cone, \(V>0\) and \((V,q)=1\), so
\[
 f(V)=g(V)\chi(V)V^{it}
\]
is an exact identity. The factor \(\chi(V)\) is evaluated using ordinary modular arithmetic. No even extension of \(\chi\) enters the analytic input. Its value is the claimed \(Q\)-independent \(\chi_{\rm odd}(4)^{-1}\). Thus the original progressions and all their parity properties remain unchanged.

## 3. Character averaging and the order of limits

The conditional odd-prime exponent average is exact. Character orthogonality for \(Q\equiv1\pmod{2^{R+1}}\) leaves precisely the characters modulo that power of two. The extra factor of two in the modulus is sufficient: a survivor with larger primitive conductor cannot be pretentiously equivalent to the chosen character whose 2-primary conductor is at most \(2^R\).

The factorization in the major-arc step needs only a bounded amplitude independent of \(Q\). That amplitude may depend on both \(N\) and \(K\); no limit for it is assumed. Its bound, together with the conditional character average, proves the required iterated vanishing for every non-survivor.

For completeness, the lower-limit argument can be written explicitly. If \(A_{K,N}(f)\) denotes the real part of the averaged correlation, its uniform lower bound gives
\[
 \liminf_K\liminf_N\int A_{K,N}\,d\sigma
 \ge\int\liminf_K\liminf_N A_{K,N}(f)\,d\sigma(f).
\]
This is Fatou applied first in \(N\), then in \(K\). The aperiodic and non-surviving pretentious terms contribute zero. Exact survivors contribute \(\Re J_\delta(t)\), which tends pointwise to 1 as \(\delta\downarrow0\). Bounded convergence then gives their full mass. The discarded conductor tail costs less than one quarter of the trivial-character atom. The positive lower bound follows without exchanging the \(N,K,\delta\) limits.

## 4. Odd dilation correspondence and scope

The odd-prime exponent boxes are a Følner sequence for the countable group of positive rationals with odd numerator and denominator. Their translates therefore give an invariant measure on the orbit closure of a color-class indicator. A positive cylinder correlation at positive odd \(U,V\) yields an actual positive odd integer dilate \(d\) with \(dU,dV\) in that color class: the empirical measures use integer elements of those boxes.

The spectral measure has a trivial-character atom at least the square of the color-class density. All relevant pair correlations are nonnegative. The parametrized values are positive, odd, and distinct on the selected cone, and the final odd dilation preserves the equation. This completes the implication for arbitrary finite colorings.

No quantitative growth rate for the finite graph chromatic numbers follows from this argument. It rules out a uniformly bounded number of colors, and hence a uniformly bounded number of P-layers in the equivalent one-prime scaffold reduction. It does not obstruct the separate full-board threshold constructions.
