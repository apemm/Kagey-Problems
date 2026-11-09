# An oblique axis rival in the two-prime CRT placement

8 November 2026. The quadratic placement
\[
 x_{ab}=4\,\operatorname{CRT}(a\bmod p,b\bmod q)
\]
excludes every tilted right angle on three marked cells when \(p,q>10h\). It does not automatically exclude oblique axis rivals. The following permitted prime choices give an exact four-black certificate.

This disproves universal mixed-collision exclusion for the unmodified rule. It does not show that every prime choice fails, or that every coloring retains the obstruction.

## 1. Parameters and exact CRT differences

Choose
\[
 w=22,\quad t=4063,\quad d=8w+1=177,\quad z=wt=89386,
\]
\[
 p=z-d=89209,\qquad q=z+d=89563,\qquad h=4469.
\tag{1}
\]
Both \(p,q\) are prime, and
\[
 10h<p<20h<q<40h.
\]
Thus (1) even meets the separated prime intervals used to bound the original construction's width.

Put \(K=(t-1)/2=2031\). Use these four double indices:

| Label | Index \((a,b)\) | Two marked rows | Physical column |
|---|---|---|---:|
| \(A\) | \((1,2209)\) | \(3,4420\) | 7,581,337,660 |
| \(B\) | \((178,2032)\) | \(357,4066\) | 7,581,695,204 |
| \(C\) | \((0,2208)\) | \(1,4418\) | 7,581,337,656 |
| \(D\) | \((177,2031)\) | \(355,4064\) | 7,581,695,200 |

All indices fit the height-\(h\) row ranges.

The column differences can also be verified without computing the large residues. Write
\[
 c_k=p\bigl(kp^{-1}\bmod q\bigr),\qquad
 \operatorname{CRT}(a,b)=a+c_{b-a}.
\]
The two diagonal indices are \(K+d\) and \(K-d\). Since \(p\equiv-2d\pmod q\), their CRT quotients differ by one unless the first quotient is \(q-1\). That wrap would require \(K+d\equiv2d\pmod q\), hence \(K=d\), which is false here. Therefore
\[
 c_{K-d}-c_{K+d}=p.
\]
The raw column difference between \(B\) and \(A\) is \(d+p=z\). The shifts from \(A\) to \(C\) and from \(B\) to \(D\) are both \(-1\).

## 2. The collision

Translate columns so that the selected point in \(A\) has column zero. The four required black points are
\[
 A=(0,3),\quad B=(357544,4066),\quad
 C=(-4,4418),\quad D=(357540,355).
\tag{2}
\]
Set
\[
 W=(-4,355),\qquad Z=(357540,4418).
\tag{3}
\]
The tilted rectangle \(R=\{A,B,W,Z\}\) has side and connector
\[
 U=B-A=(357544,4063),\qquad
 T=A-W=(4,-352).
\]
Their dot product is zero:
\[
 357544\cdot4-4063\cdot352=0.
\]
The second rectangle \(R'=\{C,D,W,Z\}\) is axis-aligned. Its diagonal \(CD\) has vector \((357544,-4063)\), so it has the same midpoint and length as \(WZ\).

Both \(W,Z\) are white in the prescribed double-only board. The column of \(W\) has marked rows \(1,4418\), and the column of \(Z\) has marked rows \(355,4064\). Thus the two presentations are both \(\{W,Z\}\). The symmetric difference of the rectangles is exactly the four required black points in (2). Subsequent singleton choices cannot repair the collision.

The parameter identity is not accidental. With general \(d=8w+1\), \(z=wt\), the relative selected points have the form
\[
 A=(0,3),\quad B=(4z,t+3),\quad
 C=(-4,t+2d+1),\quad D=(4z-4,2d+1).
\]
The perpendicularity equation reduces to
\[
 16z=2t(d-1).
\]
Whenever \(p=z-d,q=z+d\) are permitted primes and the row ranges fit, the same construction works. No claim is made that these simultaneous linear expressions are prime infinitely often.

## 3. The four double indices are independent in the Pythagorean graph

Across the two diagonal strips, every horizontal separation in this certificate exceeds \(h\), so an in-strip vertical completion is impossible.

Within either strip, the two columns have horizontal separation four. A Pythagorean vertical completion with opposite-parity rows then requires
\[
 L^2-v^2=16,\qquad L,v\text{ odd}.
\]
The only positive solution is \((L,|v|)=(5,3)\). The relevant odd vertical differences are \(4415,4419\) in the first strip and \(3707,3711\) in the second. None is three.

Consequently these four double indices have no Pythagorean graph edge between them. A proper coloring of that graph is allowed to put all four in one color class. This proves that the Pythagorean coloring condition alone does not imply exclusion of oblique rivals. A carefully chosen coloring could still separate this certificate, so this is not an obstruction to every combined coloring construction.

## 4. Independent audit of the one-prime mixed certificate

The separate construction in [one_prime_mixed_obstruction.md](one_prime_mixed_obstruction.md) was also checked independently. At \(h=9800,p=115163\), its four selected points have double indices
\[
 (1,4801),\quad(195,4803),\quad(0,4801),\quad(195,4803).
\]
They lie in the row-major columns \(4(a+pb)\). The stated \(p\) is prime, all indices fit, and the mixed vectors are
\[
 U=(922080,9605),\quad
 V=(922084,-9213),\quad H=(4,-384).
\]
Direct integer arithmetic gives \(H\cdot U=0\) and \(|U|^2=|V|^2\). The two common white columns are \(2\bmod4\), so they are empty in the double-only placement. This confirms that certificate, including its use of both cells from one double column.

The two examples have different scopes: (2) is a tilted/axis collision in the two-prime CRT rule, while the one-prime example is a tilted/tilted collision. Each disproves automatic mixed-collision exclusion for its selected allowed parameters. Neither rules out a different prime choice, a combined coloring, or a different quadratic placement.

[crt_oblique_counterexample.py](crt_oblique_counterexample.py) checks the CRT values, primality, marked rows, presentations, perpendicularity, and absence of Pythagorean edges among the four indices. Its exact output is [crt_oblique_counterexample.json](crt_oblique_counterexample.json).

## 5. A partial exclusion that survives

The strip-spacing argument does prove one useful general restriction.

**Lemma.** In the original two-prime CRT placement with \(p,q>10h\), an oblique mixed side/diagonal collision cannot have its complementary black side join same-parity rows in two different diagonal strips.

**Proof.** Write a raw column as \(n=a+c_k\), where \(k=b-a\). Let \(A,B\) be the complementary black side, \(C,D\) the complementary black diagonal, and put
\[
 N=n_B-n_A,\quad M=n_A+n_B-n_C-n_D,\quad
 U_y=y_B-y_A,\quad H_y=y_A+y_B-y_C-y_D.
\]
The mixed perpendicularity equation is
\[
 16NM+U_yH_y=0.
\]
Different strips give \(|N|>p-h/2>9.5h\), hence
\[
 |M|<h/76.
\tag{4}
\]
The quantity \(c_A+c_B-c_C-c_D\) is a multiple of \(p\). Its absolute value is at most \(|M|+|a_A+a_B-a_C-a_D|<h/76+h<p\), so it is zero. Therefore
\[
 M=a_A+a_B-a_C-a_D.
\tag{5}
\]

Suppose the side rows are odd, and set \(d=a_B-a_A\ne0\). Then \(U_y=2d\). Equality of squared lengths forces the diagonal endpoints to have the same row parity.

If they are odd, \(H_y=2M\), so perpendicularity gives \(M(4N+d)=0\). The spacing bound makes \(4N+d\ne0\), hence \(H=0\), a degeneracy.

If they are even, set \(K=k_C+k_D\). Then \(H_y=2(M-K-1)\), and
\[
 (4N+d)M=d(K+1).
\]
Reduction modulo \(p\), using \(N\equiv d\pmod p\), gives \(5M\equiv K+1\pmod p\). By (4) and \(|K+1|<h\), the congruence is the integer equality \(5M=K+1\). Substitution yields
\[
 (N-d)M=(c_B-c_A)M=0.
\]
The strips differ, so \(M=0\), and then \(H_y=0\). Again the connector vanishes.

For an even side, use \(n=b+(c_k-k)\), where \(c_k-k\) is divisible by \(q\), and repeat the argument modulo \(q\). The opposite-parity diagonal case has \(H_y=2(M+K+1)\) and gives \(5M=-(K+1)\), with the same contradiction. \(\square\)

The explicit counterexample has a mixed-parity side, so it lies outside this lemma. The lemma restricts the remaining collision hypergraph but does not bound its chromatic number.

