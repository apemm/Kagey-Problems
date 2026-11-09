# Finite multiplicative colorings cannot color the odd Pythagorean graph

9 November 2026. This result excludes a broad class of arithmetic colorings. It does not establish infinite chromatic number for arbitrary colorings.

**Theorem.** Let \(G\) be a finite abelian group and let
\[
 c:\{1,3,5,\ldots\}\longrightarrow G
\]
be completely multiplicative. There are distinct positive odd integers \(u,v\) with
\[
 c(u)=c(v),\qquad u^2+4(v-u)^2=z^2
\]
for some positive integer \(z\).

In particular, no coloring by finitely many sums of prime valuations modulo fixed integers works, even when infinitely many primes have nonzero weights. This includes the parity of the total number of prime factors. The result is stronger than failure of a fixed finite collection of local congruence tests, but it still concerns multiplicative colorings only.

## 1. Analytic inputs and their scope

The proof uses Theorem 3.1 and Propositions 4.7 and 4.9 of Frantzikinakis, Klurman, and Moreira, [Partition regularity of generalized Pythagorean pairs](https://arxiv.org/html/2407.08360v2). Their relevant consequences are:

* Correlations of an aperiodic multiplicative function along two independent linear forms, against a multiplicative function along an irreducible binary quadratic form, vanish on fixed arithmetic progressions and homogeneous convex cones.
* A pretentious multiplicative function concentrates along linear forms and irreducible binary quadratic forms on progressions avoiding small primes. The error tends to zero with the tail pretentious distance. The explicit main terms are exponentials of the corresponding weighted prime sums.

Only these analytic estimates are invoked. An unrestricted partition-regularity conclusion would not justify the odd-input restriction used here.

## 2. A finite-order concentration consequence

Let \(f:\mathbb N\to\mathbb S^1\) be completely multiplicative with finite image. If \(f\) is pretentious, it pretends to a Dirichlet character \(\chi\), with no nonzero Archimedean twist.

Indeed, if \(f\sim\chi n^{it}\), raise both functions to a common multiple of their finite orders. The pretentious triangle inequality gives \(1\sim n^{iRt}\). The prime number theorem forces \(t=0\). This is also the uniqueness argument used in Lemma 4.5 of the cited paper.

Away from the finitely many primes dividing the conductor of \(\chi\), the values \(f(p)\overline{\chi(p)}\) belong to a fixed finite set of roots of unity. Consequently
\[
 \sum_p\frac{1-\Re(f(p)\overline{\chi(p)})}{p}<\infty
 \quad\Longrightarrow\quad
 \sum_{p\nmid\operatorname{cond}(\chi)}
 \frac{|f(p)\overline{\chi(p)}-1|}{p}<\infty.       \tag{1}
\]

Put
\[
 P_1(m,n)=m^2-n^2,\qquad
 P_2(m,n)=m^2+mn-n^2.
\]
The second form has nonsquare discriminant \(5\), and \(P_2(1,0)=1\). For \(K\ge2\), choose
\[
 Q\in\Phi_K
 =\left\{\prod_{p\le K}p^{a_p}:K<a_p\le2K\right\}.
\]
For sufficiently large \(K\), every such \(Q\) is even and divisible by the conductor of \(\chi\).

Proposition 4.9, with the residue pair \((1,0)\), applies to \(P_2(Qm+1,Qn)\). Its character factor equals \(1\), its Archimedean factor equals \(1\), and its exponential prime-sum factor tends uniformly to \(1\) as \(K\to\infty\), by (1). The root-count weights in that sum are bounded, apart from finitely many irrelevant primes. Thus
\[
 \lim_{K\to\infty}\limsup_{N\to\infty}
 \max_{Q\in\Phi_K}\frac1{N^2}
 \sum_{1\le n<m\le N}
 |f(P_2(Qm+1,Qn))-1|=0.                         \tag{2}
\]

The same statement holds for \(P_1\). Here use
\[
 P_1(Qm+1,Qn)
 =[Q(m-n)+1][Q(m+n)+1]
\]
and Proposition 4.7 on each linear factor. Each possible value of \(m-n\) or \(m+n\) occurs at most \(N\) times, so the one-dimensional mean bounds control these triangular averages. Equation (1) again makes the two exponential main terms tend to \(1\).

It follows that, for a finite-order pretentious \(f\),
\[
 \lim_{K\to\infty}\limsup_{N\to\infty}
 \max_{Q\in\Phi_K}\left|
 \frac1{N^2}\sum_{1\le n<m\le N}
 f(P_1(Qm+1,Qn))\overline{f(P_2(Qm+1,Qn))}
 -\frac12\right|=0.                           \tag{3}
\]

## 3. Fourier averaging proves the theorem

For each character \(\eta\in\widehat G\), define \(f_\eta(n)=\eta(c(n))\) on odd integers and extend completely multiplicatively by \(f_\eta(2)=1\). Its image is finite.

If \(f_\eta\) is aperiodic, Theorem 3.1 applies with linear forms \(m-n,m+n\), quadratic form \(P_2\), arithmetic progression \((Qm+1,Qn)\), and cone \(m>n>0\). Therefore, for each fixed \(Q\),
\[
 \lim_{N\to\infty}\frac1{N^2}
 \sum_{1\le n<m\le N}
 f_\eta(P_1(Qm+1,Qn))
 \overline{f_\eta(P_2(Qm+1,Qn))}=0.             \tag{4}
\]
Both linear factors are independent, so the aperiodicity hypothesis occurs in the required linear factor. No conjecture about two irreducible quadratic forms is used.

There are only finitely many characters. Choose \(K\) so large that (3) has error less than \(1/(8|G|)\) for every pretentious character, and fix one \(Q\in\Phi_K\). Then choose \(N\) large enough for these bounds and for (4). Character orthogonality gives
\[
 \mathbf1_{c(P_1(M,N'))=c(P_2(M,N'))}
 =\frac1{|G|}\sum_{\eta\in\widehat G}
 f_\eta(P_1(M,N'))\overline{f_\eta(P_2(M,N'))},
\]
where \(M=Qm+1\) and \(N'=Qn\). Its average over \(1\le n<m\le N\) is positive: the trivial character contributes asymptotically \(1/2\), every other pretentious character has the same positive contribution up to the chosen error, and the aperiodic characters contribute arbitrarily little.

Choose one pair with equal colors and set
\[
 u=M^2-(N')^2,\quad
 v=M^2+MN'-(N')^2,\quad
 z=M^2+(N')^2.
\]
Since \(Q\) is even, \(M\) is odd and \(N'\) is even. Thus \(u,v\) are positive odd integers, and \(v-u=MN'>0\). Finally,
\[
 u^2+4(v-u)^2
 =[M^2-(N')^2]^2+4M^2(N')^2
 =[M^2+(N')^2]^2=z^2.
\]
This proves the theorem.

## 4. What remains open

An arbitrary finite coloring need not come from a finite multiplicative group. The argument above does not extend directly to arbitrary spectral characters: the finite-image step (1) is what makes the prime-sum phases converge to (1). Uniformly bounded chromatic number of the odd graph is therefore still unresolved by this note.

The near-quadratic full-board construction in this directory takes a different route. It does not require a bounded coloring of this graph.
