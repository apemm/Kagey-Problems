# A span-weighted bound for protected interface costs

9 November 2026. The total protected bulk-event weight crossing a fixed cut is \(O(h\log^2h)\). This improves the earlier memory-times-mean bound \(O(h\log^4h)\). It also gives an \(O(rh)\) finite-end loss for the full changed-row root family.

Let X be any protected row/column pair whose column alphabets have size \(h/2+O(1)\). Use the complete four/six positive-support family. Put \(\Lambda=1+\log h\).

**Crossing-weight claim.** Uniformly in the cut and the starting phase,
\[
 \sum_{\substack{E:\text{the black support}\\
                       \text{crosses the cut}}}\Pr(E)
 \le C h\Lambda^2.
\tag{1}
\]
The sum ranges over translated events in the infinite protected product space. The primitive norm averages, all span weights, and the exact partition-function consequences passed [independent review](crossing_bulk_independent_audit.md).

## 1. Rectangle degree and its first span moment

For a fixed corner W in the strip, let D(W) count tilted rectangles through W, and let
\[
 S(W)=\sum_{R\ni W}\operatorname{span}_x(R).
\]
The usual primitive parametrization gives
\[
 D(W)\le C h^2\Lambda^2,\qquad S(W)\le C h^4.
\tag{2}
\]

Indeed, up to constantly many orientations, the side vectors are
\[
 k(a,b),\qquad \ell(-b,a),
\]
with \(a,b,k,\ell\ge1\), \((a,b)=1\), and
\[
 kb+\ell a\le h-1.
\]
For an upper bound drop the last joint inequality and use \(k\le h/b\), \(\ell\le h/a\). The number of scale pairs is at most \(h^2/(ab)\). Their total horizontal span is at most
\[
 C h^3\left(\frac1{a^2}+\frac1{b^2}\right).
\]
Summing \(a,b\le h\) proves (2). The corner's actual row restrictions only decrease the counts.

A normalized black support with span s has at most s horizontal translates crossing a specified cut. Thus crossing sums are bounded by normalized span-weighted counts.

## 2. Hidden and horizontal four-cell supports

A hidden tilted rectangle has at most h vertical translations. Equation (2) therefore gives total normalized span weight \(O(h^5)\). Its four prescribed black rows have probability \(O(h^{-4})\), so hidden supports contribute \(O(h)\) to (1).

For a horizontal mixed support, let v be the nonzero vertical difference of the tilted black diagonal, x its horizontal difference, and d the length of the common horizontal white pair. Then
\[
 (d-x)(d+x)=v^2.
\]
For fixed v, the sum of d over all factorization choices is \(O(\sigma(v^2))\), where \(\sigma\) is the sum-of-divisors function. The black support lies inside that horizontal interval, so its span is at most d. There are \(O(h^2)\) choices for the diagonal's vertical placement and the complementary axis black row.

The elementary estimate
\[
 \sum_{v\le h}\sigma(v^2)\le C h^3
\tag{3}
\]
therefore bounds the span weight by \(O(h^5)\). To prove (3), use
\[
 \sum_{v\le h}\frac{\sigma(v^2)}{v^2}
 =\sum_{d\le h^2}\frac1d\,\#\{v\le h:d\mid v^2\}.
\]
Write \(d=ab^2\) with a squarefree. Then \(d\mid v^2\) requires \(ab\mid v\), and
\[
 \sum_{v\le h}\frac{\sigma(v^2)}{v^2}
 \le h\sum_{\substack{a\ge1\\a\ {\rm squarefree}}}
             \sum_{b\ge1}\frac1{a^2b^3}
 \le Ch.
\]
Multiply by \(h^2\). Horizontal mixed supports also contribute only \(O(h)\) to (1).

## 3. Two elementary norm averages

Let \(\varrho(d)\) count roots of \(z^2=-1\bmod d\). Prime by prime,
\[
 \varrho(d)\le r_2(d)/4.
\]
Counting lattice points in a disk and partial summation give
\[
 \sum_{d\le Y}\varrho(d)\le CY,\qquad
 \sum_{d\le Y}\frac{\varrho(d)}d\le C\log(2Y).
\tag{4}
\]

Define
\[
 R(k)=\sum_{\substack{d\mid k\\d\ {\rm odd}}}\varrho(d).
\]
Its local factor is \(2\nu+1\) at \(p^\nu\) for \(p\equiv1\bmod4\), and one at the other primes. Consequently, whenever \(r_2(N)>0\),
\[
 r_2(k^2N)\le r_2(N)R(k).
\]
Equation (4) implies
\[
 \sum_{k\le K}R(k)\le CK\log(2K),\qquad
 \sum_{k\le K}kR(k)\le CK^2\log(2K).
\tag{5}
\]

We also need a uniform primitive quadratic-divisor bound. For \(a\le h\), put
\[
 F_a(B)=\sum_{\substack{b\le B\\(a,b)=1}}r_2(a^2+b^2).
\]
The inequalities \(r_2(n)\le4\tau(n)\) and the divisor hyperbola give
\[
 F_a(B)\le
 C\sum_{d\le a+B}\varrho(d)(B/d+1)
 \le C\bigl(B\log(2(a+B))+a+B\bigr).
\tag{6}
\]
For the first inequality, every divisor \(d\mid a^2+b^2\) has \((d,a)=1\) when \((a,b)=1\). Thus b lies in at most \(\varrho(d)\) residue classes modulo d.

Partial summation in (6) yields
\[
 \sum_{\substack{b\le h\\(a,b)=1}}
 r_2(a^2+b^2)\log(2h/b)
 \le C(h+a)\Lambda.
\tag{7}
\]
In particular \(F_a(h)\le Ch\Lambda\), uniformly in a.

## 4. Nonhorizontal mixed four-cell supports

Take the complementary black side
\[
 U=k(a,b)
\]
and the perpendicular connector \(\ell(-b,a)\) of its rectangle. The alternate black diagonal has squared norm \(k^2(a^2+b^2)\), so there are at most \(r_2(k^2(a^2+b^2))\) choices.

The four required black points have horizontal span at most
\[
 C(ka+kb+\ell b).
\]
There are at most h vertical placements. Using (5), their total normalized span weight is bounded by
\[
 C h^4
 \sum_{\substack{a,b\le h\\(a,b)=1}}
 r_2(a^2+b^2)\log(2h/b)
 \left(\frac1{a^2}+\frac1{b^2}+\frac1{ab}\right).
\tag{8}
\]
The \(1/(ab)\) term is bounded by half the sum of the other two.

By (7), the \(1/a^2\) sum is \(O(h\Lambda)\). For the \(1/b^2\) sum, use \(F_b(h)\le Ch\Lambda\) and
\[
 \sum_{b\le h}\frac{\log(2h/b)}{b^2}\le C\Lambda.
\]
Thus (8) is \(O(h^5\Lambda^2)\). Multiplying by \(O(h^{-4})\) proves an \(O(h\Lambda^2)\) contribution to (1).

The vertical-side case is incompatible with one black point per column. The horizontal-side case was handled separately. All reflected orientations cost only an absolute factor.

## 5. Six-cell supports

A genuine six-cell collision consists of two tilted rectangles with one common corner W and six distinct nonshared black cells. The span of their black union is at most the sum of the two rectangle spans. For a fixed row of W, the total pair span is therefore at most
\[
 2D(W)S(W)\le C h^6\Lambda^2.
\]
Summing the h possible rows gives \(O(h^7\Lambda^2)\). Every genuine support has probability \(O(h^{-6})\), so this family contributes \(O(h\Lambda^2)\).

Counting all rectangle pairs only enlarges this upper bound; incompatible repeated-column patterns are discarded before assigning event probabilities. This completes the proof of (1).

## 6. Exact partition-function and changed-row consequences

The protected local lemma holds with \(x_E=2\Pr(E)\). Order the events internal to separate words first, then the crossing events. By (1), the conditional product bound gives
\[
 Z_X(m+n)\ge e^{-Ch\Lambda^2}
       Z_X(m)Z_{X,\mathrm{shifted}}(n).
\tag{9}
\]
This keeps every crossing rectangle; its avoidance probability is explicitly bounded rather than omitted.

For phase-period-aligned n, concatenate many n-blocks and take exponential rates. Pad at most three letters for other n, using the conditional local lemma at the partition-function level. Uniformly in n and the starting phase,
\[
 Z_X(n)\le e^{Ch\Lambda^2}\rho_X^n.
\tag{10}
\]

For the full changed-row three-black family, the missing finite-end mean is at most \(Crh\), rather than the earlier \(Crh\Lambda^2\). To see this, for each changed completion row use (2): every rectangle loses at most its full horizontal span, plus a bounded phase-period correction, in the number of admissible horizontal placements. Multiply \(S(W)=O(h^4)\) by the event probability \(O(h^{-3})\), then sum over r root rows.

Thus, in the original range \(1\le r\le h^{1-d}\) with preserved labeled class sizes,
\[
 Z_{c,X}(n)\le
 \exp[C h(\Lambda^2+r)]\,\rho_X^n
 \exp[-a r\Lambda^2n/h].
\tag{11}
\]
This is valid for all n; for short n its endpoint factor makes it a vacuous but correct bound.

Applying the domain-counting argument to (11), a language with at most
\[
 \nu_hm+O_h(1)\quad\text{protected domains},\qquad
 \nu_h=c\,\frac{r\Lambda^2}{h^2(\Lambda^2+r)},
\tag{12}
\]
has growth strictly below \(\max_X\rho_X\), after choosing c sufficiently small. Indeed the per-domain boundary cost is \(Ch(\Lambda^2+r)\), while the extensive row cost is \(ar\Lambda^2/h\); the cut entropy \(H_2(\nu_h)+\nu_h\log4\) is smaller still.

The local wall theorem supplies an additional loss \(ch\) per separated wall. The present upper bound on the protected cut cost is still \(Ch\Lambda^2\). Therefore these two inequalities alone do not determine the sign of the exact relative interface free energy, and no general dominance conclusion is drawn from them.

