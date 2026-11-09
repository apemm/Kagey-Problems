# Odd dilation averaging for the Pythagorean difference graph

9 November 2026. This note proves an odd-input adaptation of the case-(i) argument of Frantzikinakis–Klurman–Moreira. The crucial step is a varying-residue application of their quadratic concentration estimate. The [independent review](odd_folner_independent_review.md) checks the source hypotheses, character filtering, limit order, and correspondence step.

The conclusion is:

**Theorem.** Every finite coloring of the positive odd integers contains distinct same-colored \(u,v\) satisfying
\[
 u^2+4(v-u)^2=z^2.
\tag{1}
\]
Consequently the graph on the positive odd integers with these edges has unbounded chromatic number.

The analytic inputs are Theorem 3.1 and Propositions 4.7 and 4.9 of [Partition regularity of generalized Pythagorean pairs](https://arxiv.org/html/2407.08360v2). The application below uses their explicit varying-residue uniformity, not an unrestricted partition-regularity conclusion.

## 1. Odd homogeneous parametrization

Put
\[
 D(a,b)=-a^2+4ab+b^2,\qquad
 U(a,b)=ab,\qquad V(a,b)=D(a,b)/4.
\]
Whenever \(a,b\) are odd, \(D(a,b)\equiv4\pmod8\), so \(V\) is an odd integer. If \(b>a>0\), then
\[
 V-U=(b^2-a^2)/4>0.
\]
Taking \(M=(a+b)/2\), \(N=(b-a)/2\), we have
\[
 U=M^2-N^2,\quad V=M^2+MN-N^2,\quad
 Z=M^2+N^2,
\]
and hence \(U^2+4(V-U)^2=Z^2\).

For \(0<\delta<1\), use the homogeneous cone
\[
 \mathcal C_\delta=\{(x,y):0<x<y<(1+\delta)x\}.
\]
Let \(\mu_\delta\) be its area inside \([0,1]^2\), and put
\[
 w_\delta(m,n)=\mu_\delta^{-1}\mathbf1_{\mathcal C_\delta}(m,n).
\]
Its average over \([N]^2\) tends to 1. On this cone,
\[
 \frac{V(m,n)}{U(m,n)}
 =1+\frac{n^2-m^2}{4mn}
 \longrightarrow1
\]
uniformly as \(\delta\downarrow0\).

## 2. Restricted odd Følner averages

Define
\[
 \Phi_K^{\rm odd}
 =\left\{\prod_{\substack{p\le K\\p\ {\rm odd}}}p^{a_p}:
                  K<a_p\le2K\right\}.
\]
This is a multiplicative Følner sequence for the group of positive rationals with odd numerator and denominator.

Fix \(R\ge1\), set \(M_R=2^{R+1}\), and restrict to
\[
 \Psi_{K,R}=\{Q\in\Phi_K^{\rm odd}:Q\equiv1\pmod{M_R}\}.
\tag{2}
\]
For large \(K\), this set is nonempty and has relative density tending to \(1/\varphi(M_R)\).

Here is the exact character calculation. If \(g\) is completely multiplicative on odd integers and has unit-modulus values, then
\[
 \lim_{K\to\infty}
 \mathbb E_{Q\in\Phi_K^{\rm odd}}g(Q)=
 \begin{cases}
 1,&g\equiv1\text{ on odd integers},\\
 0,&\text{otherwise}.
 \end{cases}
\tag{3}
\]
Indeed, in the nontrivial case choose an odd prime \(p\) with \(g(p)\ne1\). Its exponent average over \((K,2K]\) tends to zero, and every other factor has modulus at most one.

Expanding the indicator of \(Q\equiv1\pmod{M_R}\) into the finitely many Dirichlet characters modulo \(M_R\) now gives
\[
 \lim_{K\to\infty}\mathbb E_{Q\in\Psi_{K,R}}g(Q)
 =
 \begin{cases}
 1,&g\text{ is exactly a Dirichlet character modulo }M_R
       \text{ on odd integers},\\
 0,&\text{otherwise}.
 \end{cases}
\tag{4}
\]
The same calculation with \(g=1\) proves the density assertion for \(\Psi_{K,R}\). A nonprincipal character modulo a power of two is nontrivial on some odd prime: otherwise it would be trivial on every odd integer.

## 3. Progressions with a full small-prime modulus

Set \(A=K+1\). For \(Q\in\Psi_{K,R}\), use
\[
 a=Q(2^A m+1),\qquad b=2^A Qn+1.
\tag{5}
\]
Both are odd. When \(n>m\), we have \(b>a\), so the values \(U,V\) are positive, odd, and distinct.

The full progression modulus
\[
 Q_{\rm full}=2^AQ
\]
belongs to the ordinary set \(\Phi_K\) used in the concentration propositions: its exponent of 2 is \(K+1\), and its odd-prime exponents lie in \((K,2K]\). The residue pair for the quadratic form \(D\) is \((Q,1)\).

Crucially,
\[
 \gcd(D(Q,1),Q_{\rm full})=4.
\tag{6}
\]
For each odd \(p\mid Q\), \(D(Q,1)\equiv1\pmod p\). For odd \(Q\), \(D(Q,1)\equiv4\pmod8\). Thus Proposition 4.9 applies with its normalization \(c=4\), giving the integer value \(D(a,b)/4=V(a,b)\).

The residues vary with \(Q\), but this is explicitly allowed: choose the proposition's bound \(A_K\) at least the largest \(Q\) under consideration. Its error is uniform over the admissible residues. The required divisibility by the character conductor and by all small primes holds in \(Q_{\rm full}/4\) once \(K\) is sufficiently large.

More precisely, Proposition 4.9 requires an irreducible integral binary quadratic form, an even multiplicative function that is pretentious for the form's root-count-weighted distance, a modulus in the full \(\Phi_K\), and divisibility of \(Q_{\rm full}/c\) by the character period and by every prime at most \(K\). Here the form is \(D\), of discriminant 20, and \(c=4\). Its root counts are bounded by 2 outside finitely many primes, so ordinary pretentiousness implies the required weighted pretentiousness, with a tail tending to zero. The 2-part divisibility follows from \(A-2\to\infty\), and the odd part follows from the exponents in \(Q\). Proposition 4.7 is applied only to the coprime residue 1. In both propositions the displayed exponential main term is independent of the chosen modulus and residue.

## 4. Uniform major-arc factorization

Extend every completely multiplicative character on the odd integers to \(\mathbb N\) by \(f(2)=1\), and then evenly to negative integers when applying the analytic estimates.

Suppose
\[
 f\sim\chi n^{it},
\]
and write \(\chi=\chi_2\chi_{\rm odd}\), with \(\chi_2\) of primitive conductor at most \(2^R\). The odd conductor divides \(Q\) for all sufficiently large \(K\).

Because \(Q\equiv1\pmod{2^{R+1}}\),
\[
 \frac{D(Q,1)}4\equiv1\pmod{2^R}.
\]
Modulo the odd conductor, the same integer is congruent to \(4^{-1}\). Consequently the character factor in Proposition 4.9 is the constant
\[
 \chi(V(Q,1))=\chi_{\rm odd}(4)^{-1}.
\tag{7}
\]
It does not depend on \(Q\).

Define
\[
 L_{\delta,N}(f,Q)
 =\mathbb E_{m,n\in[N]}w_\delta(m,n)\,
 f(V(a,b))\,\overline{f(U(a,b))},
\tag{8}
\]
with \(a,b\) as in (5).

To avoid any sign convention for an odd Dirichlet character on negative quadratic values, apply Proposition 4.9 to
\[
 g(n)=f(n)\overline{\chi(n)}n^{-it},\qquad n>0,
\]
extended evenly to negative integers, using comparison character 1 and twist 0. This is a multiplicative function into the closed unit disk and is pretentious to 1 for the quadratic root-count distance. Its zeros at the finitely many conductor primes are permitted and lie outside the tail once \(K\) is large.

The proposition gives an absolute-error approximation for \(g(V(a,b))\); restrict that estimate to our positive cone. On this cone \(V(a,b)>0\) and it is coprime to the conductor, so
\[
 f(V(a,b))=g(V(a,b))\chi(V(a,b))V(a,b)^{it}
\]
exactly. Here \(\chi\) is the ordinary periodic Dirichlet character on positive integers, and (7) follows from ordinary congruences. No even extension of \(\chi\) is used. In particular, the possibly negative residue value \(D(Q,1)/4\) creates no sign ambiguity. The exponential prime sum for \(g\) with trivial comparison character is exactly \(G_{D,N}(f,K)\). Thus the resulting approximation to \(f(V(a,b))\) is
\[
 \chi_{\rm odd}(4)^{-1}
 (Q_{\rm full}^2 V(m,n))^{it}\exp(G_{D,N}(f,K)).
\]
Proposition 4.7 approximates \(f(b)=f(Q_{\rm full}n+1)\) by
\[
 (Q_{\rm full}n)^{it}\exp(F_N(f,K)).
\]
The remaining linear factor is exact:
\[
 f(a)=f(Q)f(2^Am+1).
\]

It follows that there are quantities \(M_{\delta,N,K}(f)\), independent of \(Q\), such that
\[
 \lim_{K\to\infty}\limsup_{N\to\infty}
 \max_{Q\in\Psi_{K,R}}
 \left|
 f(Q)Q^{-it}L_{\delta,N}(f,Q)-M_{\delta,N,K}(f)
 \right|=0.
\tag{9}
\]
One may take
\[
\begin{split}
 M_{\delta,N,K}(f)
 ={}&\chi_{\rm odd}(4)^{-1}2^{Ait}
 \exp(G_{D,N}(f,K))\,
 \overline{\exp(F_N(f,K))}\\
 &{}\times
 \mathbb E_{m,n\in[N]}w_\delta(m,n)\,
 V(m,n)^{it}n^{-it}\,
 \overline{f(2^Am+1)}.
\end{split}
\]
The dependence on \(K\) through \(A\) is harmless. Only independence of \(Q\) is needed. The quantities are bounded by \(1+o_N(1)\): both exponential factors have modulus at most one, and the normalized weight has average tending to one.

The finite pretentious distances in the propositions make the errors in (9) tend to zero as \(K\to\infty\). The cone restriction costs only the fixed factor \(\mu_\delta^{-1}\).

Apply (4) to \(g(n)=f(n)n^{-it}\) on odd integers. Equation (9) gives
\[
 \lim_{K\to\infty}\limsup_{N\to\infty}
 \left|\mathbb E_{Q\in\Psi_{K,R}}L_{\delta,N}(f,Q)\right|=0
\tag{10}
\]
unless \(g\) is exactly a character modulo \(2^{R+1}\).

Within the present class, where the primitive 2-primary conductor of \(\chi\) is at most \(2^R\), an exact surviving \(g\) must have conductor at most \(2^R\). Otherwise two distinct Dirichlet characters would be pretentiously equivalent. Uniqueness follows from the prime number theorem in arithmetic progressions. This is the reason for restricting \(Q\) modulo one extra power of two.

For such a survivor \(f(n)=\psi(n)n^{it}\) on odd integers, both \(U(a,b)\) and \(V(a,b)\) are 1 modulo \(2^R\). Hence
\[
 f(V(a,b))\overline{f(U(a,b))}
 =\left(\frac{V(a,b)}{U(a,b)}\right)^{it}.
\]
Its normalized cone average tends, as \(N\to\infty\), to a quantity \(J_\delta(t)\), independent of \(K,Q\), satisfying
\[
 |J_\delta(t)|\le1,\qquad
 \lim_{\delta\downarrow0}J_\delta(t)=1.
\tag{11}
\]
The shifts in (5), divided by \(Q_{\rm full}\), are bounded by 1; they do not change the limiting cone integral.

## 5. The aperiodic part

If \(f\) is aperiodic, Theorem 3.1 applies to the independent linear forms \(a,b\), the irreducible quadratic form \(D\) of discriminant 20, the full modulus \(Q_{\rm full}\), and the residue pair \((Q,1)\). Complete multiplicativity and \(f(2)=1\) give \(f(D/4)=f(D)\) on these integer values.

For fixed \(K,Q,\delta\), the cone indicator in the unshifted variables differs from the shifted homogeneous cone only on \(o(N^2)\) points. Therefore
\[
 \lim_{N\to\infty}L_{\delta,N}(f,Q)=0.
\tag{12}
\]
Averaging over the finite set \(\Psi_{K,R}\) preserves this limit.

## 6. Positive spectral measures on odd dilations

Let \(\sigma\) be a finite positive measure on the compact character group of the positive odd rationals, satisfying
\[
 \sigma(\{1\})>0,\qquad
 \int f(r)\overline{f(s)}\,d\sigma(f)\ge0
 \quad\text{for all positive odd }r,s.
\tag{13}
\]
Extend the characters by \(f(2)=1\) as above.

The measurability needed here can be justified directly. Let \(\chi\) range over the countable set of primitive Dirichlet characters, and consider the relation
\[
 \mathcal R=\{(f,\chi,t):\mathbb D(f,\chi n^{it})<\infty\}.
\]
It is Borel: the squared distance is the increasing limit of continuous, nonnegative finite prime sums, and its finiteness set is Borel. The prime number theorem in arithmetic progressions gives uniqueness of the primitive \(\chi\) and real \(t\) for a given pretentious \(f\). Thus projection of \(\mathcal R\) onto \(f\) is injective. The Lusin–Souslin theorem gives a Borel image and a Borel inverse. In particular, the pretentious set, its parameter \(t\), and its primitive 2-primary conductor are measurable.

Choose \(R\) so that the \(\sigma\)-mass of pretentious characters with primitive 2-primary conductor larger than \(2^R\) is less than \(\sigma(\{1\})/4\). These exceptional sets decrease to the empty set, since each individual Dirichlet conductor is finite.

The exceptional part contributes at worst minus its mass, since all normalized averages are bounded in modulus by \(1+o_N(1)\). For fixed \(K\), the aperiodic part tends to zero as \(N\to\infty\), by (12) and bounded convergence.

On the remaining pretentious part, (10) kills every nonexact 2-primary character after the \(Q\)-average. The exact survivors contribute \(J_\delta(t)\). Bounded convergence in (11), followed by \(\delta\downarrow0\), makes their integrated real contribution tend to their total mass, which is at least \(\sigma(\{1\})\).

The relevant lower-limit interchange is legitimate: the integrands have a uniform lower bound, so Fatou's lemma can be applied first in \(N\), then in \(K\). Consequently, for sufficiently small fixed \(\delta>0\),
\[
 \liminf_{K\to\infty}\liminf_{N\to\infty}
 \int
 \mathbb E_{Q\in\Psi_{K,R}}L_{\delta,N}(f,Q)
 \,d\sigma(f)>0
\tag{14}
\]
after taking real parts.

Every individual integrated correlation in this average is nonnegative by (13), and every pair \(U,V\) is positive, odd, and distinct. Thus (14) supplies an odd pair satisfying (1) with positive spectral correlation.

## 7. From a finite coloring to the spectral measure

For completeness, the correspondence step can be carried out entirely in the odd multiplicative group.

Some color class \(\Lambda\) has positive upper density along an odd multiplicative Følner sequence. Extend its indicator to the positive odd rational group by zero off the positive odd integers. Average its translates along that Følner sequence, and pass to an invariant measure on the compact orbit closure. Let \(A\) be the cylinder where the identity coordinate equals 1. Then \(\mu(A)>0\), and positive return correlation for odd \(r,s\) implies that \(dr,ds\in\Lambda\) for some positive odd integer \(d\).

The commuting unitary dilation operators have a spectral measure \(\sigma\) for \(\mathbf1_A\). Its correlations are
\[
 \int f(r)\overline{f(s)}\,d\sigma(f)
 =\mu(T_r^{-1}A\cap T_s^{-1}A)\ge0.
\]
The projection onto constant functions gives
\(\sigma(\{1\})\ge\mu(A)^2>0\). Thus (13) holds.

Apply Section 6 and then the correspondence implication. It gives same-colored positive odd integers \(u=dU\), \(v=dV\). Homogeneity preserves (1), with \(z=dZ\). This proves the stated theorem.

The proof does not invoke a conjecture about correlations of two irreducible quadratic forms. It gives no quantitative rate for the chromatic numbers of finite initial segments. Their unboundedness follows by compactness: if every finite initial segment admitted a fixed number of colors, a consistent subsequence would color the whole countable graph with that number of colors.

