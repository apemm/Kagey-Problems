# The absolute primitive-direction coefficient

9 November 2026. The elementary hyperbola argument also gives the absolute leading coefficient. Use the notation and divisor bounds in [primitive_parity_weight_equidistribution.md](primitive_parity_weight_equidistribution.md), and put \(\delta_h=1/\log h\).

Define the convergent positive Euler product
\[
 \mathcal P=
 \prod_{p\equiv1\ (4)}
 \frac{(p-1)(p^2+4p+1)}{(p+1)^3}
 =\prod_{p\equiv1\ (4)}
 \left(1-\frac{6p+2}{(p+1)^3}\right).
\tag{1}
\]
Then each of the three primitive types satisfies
\[
 \boxed{\displaystyle
 W_T(h,\delta_h)
 \sim\frac{4\mathcal P}{3\pi^4}(\log h)^4,
 \qquad T\in\{\mathrm{OO},\mathrm{OE},\mathrm{EO}\}.}
\tag{2}
\]
This evaluates the coefficient-weighted vertical sum. The full mixed-support coefficient additionally uses the geometric orientation convention, the circle-scale integral, and the previously established negligible-range estimates.

## 1. Replace the second-coordinate progression by its density

During the proof, write \(B(N)=\pi A_N/4\), extended as in the parity note. Let
\[
 q(p)=-\frac2{p+1}\quad(p\equiv1\pmod4)
\]
and let \(q\) vanish on nonsquarefree integers and on integers containing other primes. Also write
\[
 \phi_h(b)=\frac{\log(h/b)}b.
\]
The same cutoff replacement and odd-gcd truncation used in that note give, for the OO sum with coefficient \(B\),
\[
 \begin{aligned}
 W_{\mathrm{OO}}^{B}(h,\delta_h)
 =\int_1^h\phi_h(b)
 \sum_d\frac{q(d)}d
 \sum_{\substack{m\le b/\sqrt d\\m\text{ odd}}}
 \frac{\rho(dm)}m\,
 H_{dm}(\delta_h b)\,db
 +o((\log h)^4),
 \end{aligned}
\tag{3}
\]
where
\[
 H_s(X)=\sum_{\substack{a\le X\\a\text{ odd},\ (a,s)=1}}
                  \frac{\varphi(a)}{a^2}.
\tag{4}
\]
Set \(H_s(X)=0\) when \(X<1\).

Here is the density calculation, including its factors of two. The divisor hyperbola supplies a factor two. For fixed \(a,d,m\), and an odd common divisor \(r\mid a\), the conditions on odd \(b\) give \(\rho(dm)\) progressions modulo \(2rdm\), because \((a,dm)=1\). Their density is \(\rho(dm)/(2rdm)\). The two factors cancel. After summing the Möbius coefficients, the remaining arithmetic factor is
\[
 \sum_{r\mid a}\frac{\mu(r)}r=\frac{\varphi(a)}a.
\]
The original factor \(1/a\) therefore gives (4).

For completeness, truncate \(r\) at \(D=(\log(2h))^2\). The progression-to-integral error is
\(O((\log(2h))^3\log(2D))\), by the decreasing-weight estimate in the parity proof. The discrete Möbius tail is
\(O((\log(2h))^4\log^8(2D)/D)\).
Extending the density sum back to all \(r\) costs at most
\(O((\log(2h))^4/D)\): use
\[
 \sum_{a\le X}\frac1a\sum_{\substack{r\mid a\\r>D}}\frac1r
 \ll\frac{\log(2X)}D
\]
and the convergent \(q\)-weighted root sum. The hyperbola-cutoff error is \(O((\log(2h))^3)\). All these errors are lower order in (3).

## 2. A uniform harmonic mean in the first coordinate

For odd \(s\), put
\[
 w(s)=\prod_{p\mid s}\frac p{p+1},\qquad c_0=\frac4{\pi^2}.
\]
For every fixed \(\eta>0\), uniformly for \(s\le h^2\) and \(1\le X\le h\),
\[
 H_s(X)=c_0w(s)\log X
 +O\!\left(w(s)(1+\log\log(3h))+\frac{h^\eta}{X}\right).
\tag{5}
\]
The constant in the second error term can depend on \(\eta\).

To prove this, let
\[
 R_s(Y)=\sum_{\substack{n\le Y\\n\text{ odd},\ (n,s)=1}}\frac1n.
\]
Inclusion-exclusion over the primes dividing \(2s\) gives
\[
 R_s(Y)=c_1(s)\left(\log Y+\gamma+\log2+
                       \sum_{p\mid s}\frac{\log p}{p-1}\right)
       +O\!\left(\frac{2^{\omega(s)}}Y\right),
\tag{6}
\]
where \(c_1(s)=\tfrac12\prod_{p\mid s}(1-1/p)\). The formula remains a valid bound for \(0<Y<1\), since its error then dominates the finite main expression.

The identity \(\varphi(a)/a=\sum_{r\mid a}\mu(r)/r\) implies
\[
 H_s(X)=
 \sum_{\substack{r\le X\\r\text{ odd},\ (r,s)=1}}
 \frac{\mu(r)}{r^2}R_s(X/r).
\tag{7}
\]
The coefficient of \(\log X\) is
\[
 c_1(s)\prod_{p\nmid2s}(1-p^{-2})
 =\frac4{\pi^2}\prod_{p\mid s}\frac p{p+1}.
\]
The logarithmic derivative sum in (7) is absolutely bounded, and
\(\sum_{p\mid s}\log p/(p-1)\ll1+\log\log(3h)\).
The summed error from (6) is at most
\(C2^{\omega(s)}\log(2X)/X\). The tails of the two absolutely convergent \(r\)-sums have the same required bound. Since \(2^{\omega(s)}=h^{o(1)}\) uniformly for \(s\le h^2\), this proves (5).

## 3. The weighted root coefficient

Define
\[
 S(B)=\sum_d\frac{q(d)}d
       \sum_{m\le B/\sqrt d}\frac{\rho(dm)w(dm)}m.
\tag{8}
\]
Terms with \(d>B^2\) vanish. Then
\[
 S(B)\sim\frac{\mathcal P}{\pi}\log B.
\tag{9}
\]

Fix a squarefree split-prime product \(d\). The base root count satisfies
\[
 \sum_{m\le X}\frac{\rho(m)}m=\frac1\pi\log X+O(1).
\tag{10}
\]
Compare the Euler series of \(\rho(dm)w(dm)\) with that of \(\rho(m)\). At a split prime not dividing \(d\), the correction series is
\[
 \frac{1+\alpha_p z}{1+z},\qquad
 \alpha_p=\frac{p-1}{p+1}.
\]
At a split prime dividing \(d\), including the initial factor \(2p/(p+1)\), it is
\[
 \frac{2p/(p+1)}{1+z}.
\]
The correction coefficients are absolutely summable with weight \(n^{-\sigma}\) for every fixed \(\sigma>0\). There are only finitely many primes dividing \(d\); at the others, the absolute local correction is \(O(p^{-1-\sigma})\). Thus convolution with (10) proves
\[
 \sum_{m\le X}\frac{\rho(dm)w(dm)}m=C_d\log X+O_d(1),
\tag{11}
\]
where the local factors in \(\pi C_d\) are
\[
 \begin{cases}
 1-2/(p+1)^2,&p\nmid d,\ p\equiv1\pmod4,\\
 2p^2/(p+1)^2,&p\mid d.
 \end{cases}
\tag{12}
\]

No uniform-in-\(d\) asymptotic is needed. The elementary bound
\[
 \sum_{m\le B/\sqrt d}\frac{\rho(dm)w(dm)}m
 \ll\rho(d)\log(2B)
\]
and \(\sum_d|q(d)|\rho(d)/d<\infty\) allow dominated convergence in (8), after division by \(\log B\). Therefore its leading coefficient is \(\sum_d q(d)C_d/d\). At each split prime, the combined local factor is
\[
 \left(1-\frac2{(p+1)^2}\right)
 -\frac2{p(p+1)}\frac{2p^2}{(p+1)^2}
 =\frac{(p-1)(p^2+4p+1)}{(p+1)^3}.
\]
This proves (9).

## 4. The logarithmic integral

Fix \(\varepsilon>0\). The portion of (3) with \(b\le h^\varepsilon\) is \(O(\varepsilon^3(\log h)^4)\), after taking absolute values. Indeed \(H_s(\delta_hb)\ll\log(2b)\), and the absolute root sum in (8) is \(O(\log(2b))\). The original discrete sum on the same range has this bound as well, by the primitive box estimate.

For \(b\ge h^\varepsilon\), use (5) with \(X=\delta_hb\), choosing \(\eta<\varepsilon/2\). The error from its first term is
\(O((\log h)^3(1+\log\log h))\). Its second term is negligible because \(X\ge h^\varepsilon/\log h\). Equation (3) consequently becomes, up to the stated small-range loss and a lower-order error,
\[
 c_0\int_{h^\varepsilon}^h
       \frac{\log(h/b)}b\log(\delta_h b)S(b)\,db.
\tag{13}
\]
The asymptotic (9) is uniform for all \(b\ge h^\varepsilon\), since the lower endpoint tends to infinity. Also
\(\log(\delta_hb)=\log b-\log\log h\).
The leading integral is
\[
 \int_1^h\frac{\log(h/b)(\log b)^2}b\,db
 =\frac1{12}(\log h)^4.
\tag{14}
\]
The term containing \(\log\log h\) is lower order. First let \(h\to\infty\), then let \(\varepsilon\to0\). It follows that
\[
 W_{\mathrm{OO}}^B(h,\delta_h)
 \sim\frac{\mathcal P}{3\pi^3}(\log h)^4.
\]
Restoring \(A=4B/\pi\) proves the OO case of (2). The parity theorem gives the other two cases.

## 5. An equivalent product and normalization check

The equivalent constants proposed from the fixed-first-coordinate calculation are
\[
 C_q=\prod_{p\equiv1\ (4)}\left(1-\frac4{(p+1)^2}\right),
\]
\[
 c_w=\frac12\prod_{p\equiv3\ (4)}(1-p^{-2})
       \prod_{p\equiv1\ (4)}
       \left(1-\frac{3p+1}{p^2(p+3)}\right).
\]
They satisfy the exact identity
\[
 C_qc_w=\frac4{\pi^2}\mathcal P.
\tag{15}
\]
At a split prime this follows by direct multiplication. At inert primes the factors match the Euler product for \(4/\pi^2=\tfrac12\prod_{p\text{ odd}}(1-p^{-2})\). Thus (2) is also
\[
 \frac{C_qc_w}{3\pi^2}(\log h)^4.
\]
This agreement checks the odd-coordinate density, the hyperbola factor two, and the final \(4/\pi\) scale-coefficient normalization independently.
