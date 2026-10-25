# Paper G: audit of `01_report.md`

2026-10-25. Adversarial check of the mathematics in `01_report.md`, the occupation count of the lattice walk with infinite-mean runs, $0<\alpha<1$. I ignored all status and confidence wording. For each claim: a claim card, my own derivation of the critical step (done before reading the report's proof), then each implication checked in turn. Sources were checked against the arXiv full texts. Numerics were run with my own script, which uses a different method from the report's scripts.

Scratch files (outside the repo): `audit_check.py` and `aging_check.py`, with output in `audit_out.txt`, in the session scratch folder `...\scratchpad\auditG\`.

## Verdicts

| Claim | Verdict |
|---|---|
| 1. Thm 1: local law at one point $\iff$ uniformly on compacts $\iff$ SRT$_\pm$; limit $=L_{\alpha,b}$; key bound (B2) | **Proved as written** (given the cited theorems, which I checked) |
| 2. Thm 4(a): U iff $\cos(\pi\alpha/2)\ge\alpha$, else W ($b=1$) | **Proved as written** |
| 3. Thm 2(a) fixed-$j$ layer, RV only | **Proved as written** |
| 3. Thm 2(b),(c), Cor 2.3 under (LB) | **Proved as written** (D97 checked through Berger's Thm 2.4) |
| 3. Thm 4(b) lower bound on the number of sign changes | **Correct after a stated restriction** (the $j=0$ end value; see 3.4) |
| 4. Thm 3(a) defect formula, (b) necessary condition, (f) end criterion | **Proved as written** |
| 4. Thm 3(c),(d) bulk conditions | **Proved as written under (LB$_\pm$)**, as the report says |
| 4. Thm 3(e) examples | First example proved. The second is proved at the level of orders of magnitude, and I confirmed those orders (4.5) |
| 4. Thm 3(g) aging-type start | **Incomplete.** Smallest missing piece: the near-diagonal bound $\sum_{|d-k|\le\theta N}\nu^{(N)}(d)F_{N-d}(k-d)=O(\theta^\alpha/N)$ uniformly in $k$, which needs Thm 2(b) and so (LB$_\pm$). Theorem 3's hypothesis list does not include (LB$_\pm$) |

No claim is refuted. The limit formula in (g) agrees with an independent quadrature.

---

## 0. Sources checked

- **Caravenna-Doney, arXiv 1612.07635v3 (EJP 24 (2019) paper 72).**
  - Thm 1.1, eq. (1.6): under (1.2) with $\alpha\in(0,1)\cup(1,2)$, $p>0$, and a fixed bounded $J$, $P(S_n\in x+J)\le C_0'\,\frac1{a_n}\frac n{A(x)}$ for all $n\in\mathbb N$, $x\ge0$. For a renewal law, (1.12) gives $1/A(x)\sim\bar F(x)$. So (CD1.6) in the report, $P(S_n=x)\le C\,\frac n{a_n}T(x)$, is exactly right, with no extra hypothesis. Note that (1.6) holds for all $x\ge0$, not only $x\ge a_n$, and (B2) uses it in that range.
  - Section 4.1, eq. (4.1): (SRT) holds iff $\sum_{1\le n\le A(\delta x)}P(S_n\in x+I)$ is a.n., i.e. $\lim_{\delta\to0}\limsup_x \frac{x}{A(x)}\sum\cdots=0$. It is credited to [Chi15, Appendix], and Remark 4.1 sketches both directions. This matches (CD4.1), with $A\sim1/T$. The difference between $T(n)=P(X\ge n)$ and $\bar F(n)=P(X>n)$ is $f(n)=o(T(n))$, so it is harmless.
  - Thm 1.4: for $\alpha>1/2$, SRT holds with no extra assumption. For $\alpha\le1/2$, SRT holds iff $I_1^+(\delta;x)$ is a.n., with the explicit form $\lim_\delta\limsup_x x\bar F(x)\int_{1\le z\le\delta x}F(x-dz)\frac1{z\bar F(z)^2}=0$. This matches (CD1.4).
  - (1.15) $F(x+I)\le C/(xA(x))$ is (LB), credited to Doney 1997 in the arithmetic case.
  - With SPAN, the arithmetic span is 1, so $I=(-1,0]$ and $P(S_n\in x+I)=P(S_n=x)$.
- **Berger, arXiv 1706.07924v4 (PTRF 175 (2019)), Thm 2.4, eq. (2.9).** Assume (1.1), $\alpha\in(0,2)$, and (2.5): $P(X=x)\le C_1L(x)(1+x)^{-1-\alpha}$, which is (LB). Then $P(S_n=x)\le C\,nL(x)x^{-1-\alpha}\asymp nT(x)/x$ for $x\ge a_n$. The paper says this extends Doney 1997 Thm A. So (D97) as used in the report is correct.

---

## 1. Theorem 1 (local Lamperti law)

**Claim card.** Assume (RV$_\alpha$) (both tails RV with index $-\alpha$, $T_-/T_+\to b\in(0,\infty)$) and (SPAN), with a fresh start of either sign. Then:
- (a) $\Lambda=L_{\alpha,b}$;
- (b) local law at one $x_0$ $\iff$ local law uniformly on compacts $\iff$ SRT$_+$ and SRT$_-$;
- (c) by CD Thm 1.4: no condition is needed for $\alpha>1/2$, and for $\alpha\le1/2$ the law holds iff $I_1^+$ is a.n. for both laws.

### 1.1 My derivation of the critical step (B2) first

$q_{m+1}(k)=P(S_m<k\le S_{m+1})$. I split according to where $S_m$ is.
- $S_m<k/2$: the next run must exceed $k/2$, which costs $\le T(k/2)\le CT(k)$.
- $S_m=k-i$ with $i\le k/2$, in dyadic shells $i\in[2^l,2^{l+1})$: the contribution is $\le T(2^l)\,P(S_m\in(k-2^{l+1},k-2^l])$.

The window has $2^l$ lattice points, each at height $\ge k/2$. So by (1.6) the window probability is $\le 2^l\cdot Cm\,T(k)/a_m$, and by (A1) it is also $\le CmT(k)$.
- Shells with $2^l\le a_m$ give $\frac{CmT(k)}{a_m}\sum_{2^l\le a_m}2^lT(2^l)\le CmT(k)T(a_m)$, a geometric sum of an RV function with index $1-\alpha>0$.
- Shells with $2^l>a_m$ give $CmT(k)\sum_{2^l>a_m}T(2^l)\le CmT(k)T(a_m)$ (Potter).
- Finally $mT(a_m)\le C$.

So $q_{m+1}(k)\le CT(k)$ uniformly in $m$, under RV alone. This is the report's proof. It is correct, and it is the only place where (1.6) is needed for $x$ far below $a_m$ as well as above it, which (1.6) allows.

I also checked the auxiliary bounds.
- (A1): $E[X;X<x]\le\sum_{n<x}T(n)\le CxT(x)$ by Karamata.
- (A2) is immediate.
- (A3): $u_m(x)\le P(S_h\le x)\sup u_{m-h}$, with $\sup_x u_n(x)\le C/a_n$ from Gnedenko for every $n$.
- (B3): the identity $q_m(j)=\sum_s u_h(s)q_{m-h}(j-s)$ holds (split $S_{m-1}=S_h+$ the rest). The two pieces are bounded correctly. For $h\gtrsim1/T(j)$ we get $a_h\gtrsim j$, so $jT(j)/a_h\le CT(j)$.
- (B1): the Riemann-sum error is $o(1/a_m)\cdot\sum_{i\le N}T(i)=o(T(N))$, and the near-diagonal error is $C\theta^{1-\alpha}T(N)$.

### 1.2 Decomposition

From scratch, with a fresh plus start and $k+j=N$:
- if step $N$ is plus, $m$ minus runs are complete with total exactly $j$, and the $(m+1)$-th plus run covers $k$, which gives $u^-_m(j)q^+_{m+1}(k)$;
- if step $N$ is minus, $m$ plus runs total exactly $k$, and the $m$-th minus run covers $j$, which gives $u^+_m(k)q^-_m(j)$.

This is the report's identity. My script computes $P_N$ from this sum (FFT convolution powers, then dot products over $m$), and it agrees with brute force over all sign strings to $1.1\cdot10^{-16}$ for $N=8,11$ and $\alpha=0.4,0.8$.

### 1.3 Implications checked

1. **Medium $m$.** $u^-_m(j)=a_m^{-1}[g_b(j/a_m)+o(1)]$ (Gnedenko under SPAN). $q^+_{m+1}(k)=T_+(N)[Q_t(x)+o(1)]$ by (B1). $a_{m}/N\to t^{1/\alpha}$, with mesh $T_+(N)$ in $t$. For the minus kernel, the factor $b$ inside $Q^b_t$ accounts for $T_-(N)\sim bT_+(N)$. The scaling is consistent: Lévy tail $r^{-\alpha}$ gives Laplace exponent $\Gamma(1-\alpha)\lambda^\alpha$. Correct.
2. **Large $m$.** By (A3) and (B2), $T_+(N)\sum_{m>\delta^{-1}/T}a_m^{-1}e^{-cmT(N)}\le \frac CN\int_{1/\delta}^\infty t^{-1/\alpha}e^{-ct}dt$. Correct for both terms.
3. **Small $m$, sufficiency.** (B2) gives $q\le CT$, so $N\cdot\mathrm{Term1_{small}}\le C\,NT(N)\sum_{m<\delta/T_+(N)}u^-_m(j)$. With $j\asymp N$: $NT_+(N)\asymp jT_-(j)$, and $\delta/T_+(N)\le A_-(\delta'j)$ with $\delta'=\delta'(\delta)\to0$. Then (4.1) under SRT$_-$ gives $\lim_\delta\limsup_N=0$, uniformly in $k/N\in[x_1,x_2]$, because (4.1) has a limsup over all $x$. Term 2 is the same with SRT$_+$. Correct.
4. **Necessity.**
   - Lower bound: $q^+_{m+1}(k)\ge P(S_m<k/2)T_+(k)$, and $P(S_m\ge k/2)\le CmT(k/2)\le C\delta x_0^{-\alpha}$, so $q\ge\frac12T_+(N)$ for small $\delta$.
   - Nonnegativity of every term gives $\frac12NT_+(N)\sum_{m<\delta/T}u^-_m(j_N)\le NP_N(k_N)-N\,\mathrm{Term_{med}}\to L(x_0)-\Lambda_\delta(x_0)$. This tends to $0$ as $\delta\to0$, by monotone convergence and (a).
   - The transfer from $N$ to $j$ is valid: $N\mapsto j_N=N-\lfloor x_0N\rfloor$ has increments 0 or 1, so it is onto the large integers, and $\limsup_j g(j)\le\limsup_N g(j_N)$.
   - For $j=j_N$, $A_-(\delta''j)\le\delta/T_+(N)$ with $\delta''\to0$. Monotonicity in $\delta''$ then gives (4.1) for the minus law, hence SRT$_-$.
   - Term 2 with $k_N$ gives SRT$_+$.
   - A single point $x_0$ therefore forces both SRTs. Correct.
5. **Fresh minus start.** Only the index shift $q_m\leftrightarrow q_{m+1}$ changes, and no limit is affected. Correct.
6. **(a), my own computation.**
   - Laplace transforms: $\mathcal L[Q_t](\lambda)=e^{-t\Gamma\lambda^\alpha}\Gamma(1-\alpha)\lambda^{\alpha-1}$. Integrating in $t$ gives $(\lambda^{\alpha-1}+b\mu^{\alpha-1})/(\lambda^\alpha+b\mu^\alpha)$.
   - Homogeneity: substituting $s=tc^{-\alpha}$ gives degree $-1$.
   - Change of variables $x=sv$, $y=s(1-v)$, $dx\,dy=s\,ds\,dv$, which gives (2.1).
   - Continuation: $1-1/z\in(-\infty,0]$ iff $z\in(0,1]$, so the principal branch is analytic on $\mathbb C\setminus[0,1]$, and the identity extends from real $z>1$.
   - Boundary value: at $z=x+i0$, $1-1/z=we^{i\pi}$ with $w=(1-x)/x$. Then $-\frac1\pi\mathrm{Im}\,G=\frac{\sin\pi\alpha}{\pi}\frac{b\,w^{\alpha-1}(1+w)}{x(b^2+2bw^\alpha\cos\pi\alpha+w^{2\alpha})}$. Multiplying through by $x^{2\alpha}$ gives exactly $L_{\alpha,b}$.
   - Mean: $-F'(0)=1/(1+b)$, which is the right direction (if $b<1$, plus runs are heavier and plus occupies more).
   - All of this is correct. Continuity of $\Lambda$ (needed for "everywhere" rather than "a.e.") follows by dominated convergence and could be stated in one line.
7. **(c)** follows from (b) and CD Thm 1.4, including $\alpha=1/2$, which Thm 1.4 covers.

**Verdict: proved as written.** The key bound (B2) is correct under RV alone, using exactly CD (1.6).

---

## 2. Theorem 4(a) (shape, $b=1$)

**Claim card.** $L_{\alpha,1}$ has exactly one critical point iff $\cos(\pi\alpha/2)\ge\alpha$, and exactly three otherwise (local maximum at $1/2$, two minima).

**My derivation.**
- Change of variable: put $w=(1-x)/x=e^t$. Then $x^{\alpha-1}(1-x)^{\alpha-1}=x^{2\alpha-2}w^{\alpha-1}$, and the denominator is $x^{2\alpha}w^\alpha\cdot2(\cosh\alpha t+c)$. Since $x^{-2}w^{-1}=(1+w)^2/w=2+2\cosh t$, we get $L\propto(1+\cosh t)/(\cosh\alpha t+c)$, and $x\mapsto t$ is a decreasing bijection.
- Sign of the derivative: $\phi'$ has the sign of $\tanh(t/2)(\cosh\alpha t+c)-\alpha\sinh\alpha t$, i.e. for $t>0$ the sign of $\chi=\cosh\alpha t+c-\alpha\sinh\alpha t\coth(t/2)$.
- Monotonicity of $G=\chi-c$: with $s=t/2$, I get $G'=\frac{\alpha}{\sinh^2s}\cdot\frac12[\sinh\alpha t\cosh t-\alpha\cosh\alpha t\sinh t]$, using $\sinh^2s+\frac12=\frac12\cosh t$ and $\cosh s\sinh s=\frac12\sinh t$. Then $n'(t)=(1-\alpha^2)\sinh\alpha t\sinh t>0$ and $n(0)=0$, so $G$ is strictly increasing.
- Endpoints: $G(0+)=1-2\alpha^2$, and $G\sim\frac{1-\alpha}2e^{\alpha t}\to\infty$.
- Conclusion: if $1+\cos\pi\alpha-2\alpha^2\ge0$, i.e. $\cos(\pi\alpha/2)\ge\alpha$, then $\chi>0$ on $(0,\infty)$ and the shape is U. Otherwise $\chi$ has exactly one zero, which gives the W shape.

Numerics: the root of $\cos(\pi\alpha/2)=\alpha$ is $0.594611644056836$. On a grid of $2\cdot10^5$ points, $L$ has 1 critical point at $\alpha=0.55,0.59,0.5946$ and 3 at $\alpha=0.5947,0.60,0.7,0.9$. The exact law matches: $\alpha=0.58$ gives 1 sign change at $N=1000,2000,4000$; $\alpha=0.61$ gives 3, at $k=344,500,656$ for $N=1000$.

**Verdict: proved as written** for $b=1$. The case $b\neq1$ is explicitly left unproved in the report and is not claimed.

---

## 3. End layers

### 3.1 Thm 2(a) (fixed $j$, RV only)

**My derivation.**
- Term 1, $m\le j$ fixed: $q_{m+1}(k)=P(S_{m+1}\ge k)-P(S_m\ge k)\sim(m+1)T(k)-mT(k)=T(k)$, by subexponentiality.
- Term 2: $u^+_m(N-j)\le m\sup_{s\ge (N-j)/m}f(s)=o(T(N))$, since $f=o(T)$ under RV.
- Hence $P_N(N-j)=T_+(N)\sum_m u^-_m(j)+o=T_+(N)u_-(j)+o(T_+(N))$. The report proves the same thing through the final-run identity.

**Verdict: proved as written.**

### 3.2 Thm 2(b) (uniform matching under (LB$_+$), SRT$_-$)

Checks:
- $T_+(N)u_-(j)\Phi_b(j/N)=N^{-1}L(1-j/N)(1+o(1))$ under SRT. I verified this algebra, and it agrees with the definition of $\Phi_b$.
- On $\varepsilon N\le j\le(1-\delta)N$ the claim is Theorem 1. That needs SRT$_+$, which follows from (LB$_+$) by Doney.
- Term 1 for $j\le\varepsilon N$:
  - lower bound $(1-C\eta\theta^{-\alpha})T(N)$;
  - upper bound: the part $r<\theta N$ is $\le T(k-\theta N)$. The part $r\ge\theta N$ uses (D97), valid because $\theta N\ge a_M$ when $\eta\le(\theta/2)^\alpha$. This gives $C\eta\theta^{-1-\alpha}T(N)=C\eta^{1/2}T(N)$ with $\theta=\eta^{1/(2+2\alpha)}$.
  - The tail $\sum_{m>M}u^-_m(j)\le\frac{C}{jT_-(j)}\varphi(MT_-(j))$ with $MT_-(j)\gtrsim\eta\varepsilon^{-\alpha}\to\infty$.
  - All correct.
- Term 2 for $j\le\varepsilon N$:
  - For $m\le c'/T(N)$: (D97) and (B3) give $\le CT(N)/(NT_-(j))$, which is $\le C(j/N)T(N)u_-(j)$.
  - For larger $m$: the bound is $\frac CNe^{-c''s}$ with $s=T_-(j)/T(N)\gtrsim\varepsilon^{-\alpha}$. Relative to $T(N)u_-(j)$ this is $\lesssim (j/N)\,s\,e^{-c''s}\to0$.
  - Correct.
- The order of limits works: choose $\eta$, then $\varepsilon(\eta)$, then $N\to\infty$, then $\eta\to0$.

**Verdict: proved as written** under the stated hypotheses. The missing lemma (M0) for the case without (LB) is correctly identified as open.

### 3.3 Thm 2(c), Cor 2.3, Remark 2.4

- (c): with pure power tails, $T_-(j)/T_+(N)=b(j/N)^{-\alpha}$ exactly in the limit, and $u\asymp\omega$ for large $j$ turns $o(\omega)$ into a relative $o(1)$. Correct.
- Cor 2.3: the bulk is $\le C/N$, the intermediate layer is $\le CT(N)\omega(J)$, and $NT(N)\to\infty$. Correct.
- Remark 2.4: correct. At $\alpha=1/2$, $2\int_0^{\varepsilon}L=\frac4\pi\arcsin\sqrt\varepsilon$, which gives 0.2277 at $N=1000$, as stated.

### 3.4 Thm 4(b) (lower bound) and the restriction

The argument is correct. The count of sign changes of the differences of a subsequence is at most the count for the full sequence. The junction between bulk samples (increasing toward each end) and end samples ($T(N)\kappa(J)\gg1/N$, with $\kappa$ decreasing in $j$) adds no sign change.

Restriction needed: Thm 3(f) gives $P_N(N)=Q_+(N)+T_+(N)\kappa_+(0)+\dots$ with $\kappa_+(0)=0$ by its own formula. So the end value at $j=0$ is $\lim Q_+(N)/T_+(N)$, not $\kappa_+(0)$. The "explanation of the counts" uses $\kappa(0)=1/2$, which is $Q_+(N)/T(N)$ for the fair start. In 4(b), $\kappa_\pm(0)$ should therefore be defined as $\lim Q_\pm(N)/T_\pm(N)$, assuming that limit exists. For a general initial run it need not converge, and then the $j=0$ sample can break the copied pattern. With that definition and assumption the statement is correct. Numerically, for the fair start, $P_N(N)/T(N)=0.5000$ exactly, and $P_N(N-1)/T(N)$ is 0.5754, 0.5737, 0.5727 at $\alpha=0.9$, tending to $f(1)=0.5715$.

---

## 4. Theorem 3 (initial run)

**Claim cards.**
- (a) Defect formula for any fixed initial run with $D<\infty$.
- (b) Local law at one point $\Rightarrow\nu_\pm(n)=o(1/(nT_\mp(n)))$.
- (c) Under (LB): $n\nu_\pm(n)\to0\Rightarrow$ local law.
- (d) Under (LB) and $u_\pm>0$: an exact criterion.
- (e) Examples.
- (f) End criterion $W^+_N=o(T_+(N))$.
- (g) Aging-type limit.

**My derivation of (a) first.** Condition on the first run. A plus first run of length $d$ leaves a fresh minus walk of length $N-d$ that needs $k-d$ plus steps.
- $d<\varepsilon N$: Theorem 1 applies, uniformly over the horizon, so this part gives $\pi_+L(k/N)+O(\varepsilon)$.
- $\varepsilon N\le d<k/2$: the ratio $(k-d)/(N-d)\in[x_1/2,x_2]$, so this part is $O(P(D\ge\varepsilon N))$.
- $d\in[k/2,k]$: this is $\mathcal D^+$.

The minus side is the same with $d\le N-k$, and $k/(N-d)\le x_2/(x_2+(1-x_2)/2)<1$. This matches the report.

### 4.1 (a)
Proved as written (uses SRT$_\pm$ through Theorem 1).

### 4.2 (b)
The terms $d=k$ and $d=N-k$ are exact: $N\nu_+(k)T_-(N-k)$ and $N\nu_-(N-k)T_+(k)$. Both $k_N$ and $N-k_N$ run through all large integers. Proved.

### 4.3 (c), (d)
- $F^-_n(i)=T_-(n)[u_+(i)\Phi(i/n)+o(\omega_+(i))]$ for $i\le k/2$ comes from Thm 2(b) at the minus end, which needs (LB$_-$) and SRT$_+$. Here $i/n\le x_2/(2-x_2)<1$.
- Then $\sum_{i\le k}\omega_+(i)\sim1/(\alpha T_+(k))$ gives (c).
- For (d), $u_+\asymp\omega_+$ needs $u_+(i)>0$ for all $i$ together with SRT. The $o(\omega)$ error is uniform, so $\mathcal D^+\asymp NT(N)\sum\nu_+(k-i)\omega_+(i)$ in both directions.
- Proved under (LB$_\pm$).

### 4.4 (f)
- Plus part with $d\le N/2$: Thm 2(a) applies over the horizon range $[N/2,N]$, and dominated convergence gives $\pi_+T(N)u_-(j)\mathbf 1_{j\ge1}$.
- $d>N/2$: this part is exact.
- Minus part: $d\le j$, a finite sum.
- "If" direction: $\Pi^-_m(j)\le C_jT_+(m)$.
- "Only if" direction: $\Pi^-_m(j^*)\ge cT_+(m)$ for $m\ge m^*$, and $\Pi^-_m(m)=T_-(m)>0$ for $m<m^*$. Nonnegativity then isolates each term.
- Sufficiency of $n\nu\to0$, and the fresh-start case, are both correct.
- Proved as written (RV only).

### 4.5 (e)
- **First example.** The term $d=k$ gives $c\,b\,x_0^{\alpha-1}(1-x_0)^{-\alpha}$. I verified the constant from $T_-(N-k)/T_+(k)\to b((1-x_0)/x_0)^{-\alpha}$. Proved.
- **Second example**, $\sqrt n$ masses $T(\sqrt n)/(nT(n))$ just below $n=n_i$:
  - (b) holds, because $T(\sqrt n)\to0$;
  - the (d) sum at $k=n_i$ is $NT(N)\cdot\frac{T(\sqrt n)}{nT(n)}\cdot\sum_{i\le\sqrt n}\omega(i)\asymp\frac{T(\sqrt n)}{\alpha T(\sqrt n)}=1/\alpha\not\to0$, so (d) fails;
  - the cluster mass $\sqrt nT(\sqrt n)/(nT(n))\to0$ is summable along a sparse sequence.
  - The orders are confirmed. Writing it out needs only the constants.

### 4.6 (g)
- The formula is the natural Riemann sum: a first run of length $zN$ is followed by a fresh walk of length $(1-z)N$.
- An independent quadrature at $\alpha=1/2$, with $D$ uniform on $\{1,\dots,N/2\}$ (so $\rho_\pm=1$ on $(0,1/2)$), gives 0.869420 at $x=0.3$ and 1.273240 at $x=0.5$. The second is exactly $2L(1/2)=4/\pi$. Both agree with the report.
- The outline omits two things:
  1. The near-diagonal estimate. For $z$ near $x$ the remainder is in its end layer, with $F\le CT(N)\omega(i)$. Combined with $\nu^{(N)}\le C/N$ this gives $\sum_{i\le\theta N}\frac CNT(N)\omega(i)\le C\theta^\alpha/N$. The bound needs Thm 2(b), hence (LB$_\pm$).
  2. The same estimate at $z\to1-x$ on the minus side.
- Both are routine once (LB$_\pm$) is added to the hypotheses of (g).
- **Incomplete** as written, but the gap is bookkeeping, not an idea.

---

## 5. Numerics (independent recursion)

The method is the run-index decomposition of 1.2, with $u_m$ from FFT convolution truncated to $[0,N]$, which is exact because the supports are nonnegative. The law is symmetric zeta with a fair start, and the total mass is 1 to 12 digits.

| $\alpha$ | $N$ | $NP_N(N/2)/L(1/2)$ | $x=0.1$ ratio | sign changes (positions) |
|---|---|---|---|---|
| 0.5 | 1000 / 2000 / 4000 | 1.0149 / 1.0105 / 1.0075 | 1.0079 / 1.0058 / 1.0042 | 1 (at $N/2$) |
| 0.58 | 1000 / 2000 / 4000 | 0.9846 / 0.9863 / 0.9883 | 1.0059 / 1.0045 / 1.0034 | 1 |
| 0.61 | 1000 / 2000 / 4000 | 0.9696 / 0.9739 / 0.9781 | 1.0139 / 1.0113 / 1.0090 | 3 (344, 500, 656 at 1000) |
| 0.9 | 1000 / 2000 / 4000 | 0.4903 / 0.5168 / 0.5433 | 2.1791 / 2.0402 / 1.9196 | 5 (1, 142, 2000, 3858, 3999 at 4000) |

These match the report's values to all printed digits. The U/W switch falls between 0.58 and 0.61, on both sides of $\alpha_c=0.59461$, as Thm 4(a) predicts. The count 5 at $\alpha=0.9$ includes the two end extrema at $k=1$ and $k=N-1$, as explained in Thm 4.

## 6. Minor points (no effect on the verdicts)

- The report's (CD4.1) and (CD1.4) are written with $T=P(X\ge n)$, while CD use $\bar F=P(X>n)$. These are asymptotically equivalent, and the $\delta\to0$ limit absorbs the constants.
- In 2.4, state that $\Lambda$ is continuous on $(0,1)$ (dominated convergence) before inverting pointwise.
- Theorem 3's header lists SRT$_\pm$, but (c), (d) and (g) use (LB$_\pm$). Put that in the hypotheses of each part, not only in the text.
- Thm 4(b): define $\kappa_\pm(0)$ as $\lim Q_\pm(N)/T_\pm(N)$ (3.4).
