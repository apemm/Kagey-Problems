# Paper G: the occupation count of the lattice Levy walk with infinite-mean runs

Research notes, 2026-10-25. The walk, notation and exact identities are those of Paper F
(`kagey-problems/problem131/paperF/sec_setting.tex`): alternating runs, run laws $f_\pm$, tails
$T_\pm(n)=P(X_\pm\ge n)$, convolution powers $u^\pm_m=f_\pm^{*m}$, renewal sequences $u_\pm$,
covering kernels $q^\pm_m(k)=\sum_{r<k}u^\pm_{m-1}(r)T_\pm(k-r)$, the fresh-plus identity
(Prop. fresh-identity), the first-run decomposition (Prop. first-run), the final-run identity
(Prop. final-run), and $A_N$ = number of plus steps, $P_N(k)=P(A_N=k)$. Nothing in Paper F was edited.

Predictions were written first (`00_predictions.md`); all nine came out as predicted (Section 7).

---

## 0. Summary

| Item | Status |
|---|---|
| Thm 1: local Lamperti law, fresh starts. Holds at one point $\iff$ uniformly on compacts $\iff$ SRT for both run laws. So: unconditional for $\alpha>1/2$; for $\alpha\le1/2$ iff the Caravenna-Doney condition holds for both laws | **Proved** (Section 2), modulo cited theorems (Gnedenko LLT, Caravenna-Doney Thm 1.1 and Thm 1.4 with its reformulation (4.1)) |
| Identification of the limit with Lamperti's density, self-contained (Laplace transform + Stieltjes inversion) | **Proved** (2.4) |
| Thm 2(a): fixed-$j$ boundary layer, $P_N(N-j)=T_+(N)\kappa(j)+o(T_+(N))$, RV only | **Proved** (routine; same as F Thm C(d)) |
| Thm 2(b): uniform matching of layer and bulk, $0\le j\le(1-\delta)N$ | **Proved under (LB)** (Doney's local condition). Under SRT alone: open, one named missing lemma |
| Cor 2.3: the global mode sits at bounded distance from an end, for every $\alpha\in(0,1)$ | Proved under (LB) |
| Thm 3: the initial run (Wang-Schulz-Deng-Barkai question), exact defect, sharp end criterion, bulk criteria, examples, scale-$N$ (aging-type) starts | (a), (b), (e), (f) proved; (c), (d) proved under (LB); (g) proved in outline |
| Thm 4(a): the symmetric Lamperti density has exactly 1 critical point iff $\cos(\pi\alpha/2)\ge\alpha$ ($\alpha\le0.5946\ldots$), else exactly 3 | **Proved** (the value 0.5946 is in Margolin-Barkai 2006; the closed form and the proof of "exactly" I did not find) |
| Thm 4(b): lower bound on the number of sign changes of $\Delta P_N$: $\sigma_L+\sigma_++\sigma_-$ | Proved |
| Exact count (equality) for large $N$ | Conjecture; two named missing lemmas. Matches every computed case |
| Plan's numbers (1.015, 1.011, 1.007; counts 1, 1, 3, 5) | **Reproduced** by an independent recursion |

Two corrections to the plan (item 2): (i) the end layers do **not** carry a positive fraction of
the mass; the mass within $o(N)$ of the ends tends to zero (Remark 2.4). What is true is that the
end values dominate pointwise: $T(N)\gg1/N$, so the atoms and layers are far above the bulk density,
and the global mode is at an end for every $\alpha\in(0,1)$. (ii) The count 5 at $\alpha=0.9$ is not
a bulk effect; it is $3$ (W-shaped density) $+2$ (one extra end extremum at each end, because the fair
start halves the atom: $\kappa(0)=1/2<\kappa(1)=f(1)=1/\zeta(1.9)=0.5715$).

---

## 1. Hypotheses and notation

- (RV$_\alpha$) $T_\pm$ regularly varying with the same index $-\alpha$, $0<\alpha<1$, and
  $T_-(n)/T_+(n)\to b\in(0,\infty)$. (Unequal indices or $b\in\{0,\infty\}$ give a degenerate
  global limit and are not treated.)
- (SPAN) as in F: the support of $X_\pm$ lies in no progression $c+h\mathbb Z$, $h\ge2$.
- (SRT$_\pm$) $u_\pm(n)\sim\dfrac{\sin\pi\alpha}{\pi}\,\dfrac1{nT_\pm(n)}$.
- (LB$_\pm$) $f_\pm(n)\le C\,T_\pm(n)/n$ for all $n\ge1$ (Doney's condition; CD (1.15)).

Scale: $a(t)$ increasing with $tT_+(a(t))\to1$; $a_m=a(m)$; RV index $1/\alpha$. For $t>0$ put
$m_N(t)=\lfloor t/T_+(N)\rfloor$; then $a_{m_N(t)}/N\to t^{1/\alpha}$ uniformly on compact $t$-sets.
$g$ is the density of $Z$ with $Ee^{-\lambda Z}=e^{-\Gamma(1-\alpha)\lambda^\alpha}$;
$p_t(z)=t^{-1/\alpha}g(zt^{-1/\alpha})$ and $p^b_t(z)=(bt)^{-1/\alpha}g(z(bt)^{-1/\alpha})$ (densities of
stable subordinators with Laplace exponents $t\Gamma(1-\alpha)\lambda^\alpha$, $bt\Gamma(1-\alpha)\lambda^\alpha$,
Levy tails $r^{-\alpha}$, $br^{-\alpha}$). Covering densities:
$$Q_t(x)=\int_0^xp_t(z)(x-z)^{-\alpha}dz,\qquad Q^b_t(y)=b\int_0^yp^b_t(z)(y-z)^{-\alpha}dz .$$
Lamperti density, $c=\cos\pi\alpha$:
$$L_{\alpha,b}(x)=\frac{\sin\pi\alpha}{\pi}\,\frac{b\,x^{\alpha-1}(1-x)^{\alpha-1}}{b^2x^{2\alpha}+2bc\,x^\alpha(1-x)^\alpha+(1-x)^{2\alpha}} .$$
Its mean is $1/(1+b)=\lim T_+/(T_++T_-)$. In the variable $t=\log((1-x)/x)$, $\beta=\log b$:
$$L_{\alpha,b}(x)=\frac{\sin\pi\alpha}{\pi}\,\frac{1+\cosh t}{\cosh(\alpha t-\beta)+\cos\pi\alpha}. \tag{1.1}$$
$\omega_\pm(i)=\min(1,1/(iT_\pm(i)))$. Under SRT, $u_\pm\le C\omega_\pm$.

### 1.1 Tools (cited)

- (G) Gnedenko's local limit theorem [BGT89, Thm 8.4.1; as used in CD (2.6)]: under (RV),(SPAN),
  $\sup_x|a_mu^+_m(x)-g(x/a_m)|\to0$; likewise $u^-_m$ with $g$ replaced by the density $g_b$ of
  $b^{1/\alpha}Z$. Hence $\sup_xu_m(x)\le C/a_m$ for all $m\ge1$.
- (CD1.6) Caravenna-Doney, EJP 24 (2019) paper 72, Thm 1.1, eq. (1.6): under (1.2) alone
  (here: $T$ RV, $\alpha\in(0,1)$), for all $n\ge1$, $x\ge0$: $P(S_n=x)\le C\,\dfrac{n}{a_n}\,T(x)$.
- (CD4.1) Same paper, Section 4.1: (SRT) holds iff
  $\lim_{\delta\to0}\limsup_x xT(x)\sum_{1\le n\le A(\delta x)}P(S_n=x)=0$, $A=1/T$ (credited there to
  [Chi15, Appendix]).
- (CD1.4) Same paper, Thm 1.4 (renewal case): for $\alpha>1/2$ SRT holds with no extra assumption;
  for $\alpha\le1/2$ it holds iff $I_1^+(\delta;x)$ is a.n., explicitly
  $\lim_{\delta\to0}\limsup_x xT(x)\sum_{1\le z\le\delta x}P(X=x-z)\,\frac1{zT(z)^2}=0$.
  Sufficient: (LB) (Doney 1997 arithmetic case; CD (1.15)); sharper: CD Prop. 1.7.
- (D97) Doney, PTRF 107 (1997) 451-465, Theorem A (as restated in Berger, PTRF 175 (2019), Thm 2.4,
  which says it extends Doney's Theorem A): under (LB), $P(S_n=x)\le C\,n\,T(x)/x$ for $x\ge a_n$.

### 1.2 Elementary bounds (proved here; $X\ge1$, $T$ RV index $-\alpha\in(-1,0)$)

(A1) $P(S_m\ge x)\le C\,mT(x)$ for all $m,x\ge1$. *Proof.* $P(S_m\ge x)\le mT(x)+P(\sum X_i1\{X_i<x\}\ge x)\le mT(x)+mE[X;X<x]/x$ and $E[X;X<x]\le\sum_{n<x}T(n)\le CxT(x)$ (Karamata). $\square$

(A2) $P(S_m<x)\le(1-T(x))^m\le e^{-mT(x)}$.

(A3) $u_m(x)\le C\,e^{-(m/2)T(x+1)}/a_m$ for $m\ge2$. *Proof.* With $h=\lfloor m/2\rfloor$,
$u_m(x)\le P(S_h\le x)\sup_yu_{m-h}(y)\le e^{-hT(x+1)}C/a_{m-h}$, and $a_{m-h}\ge ca_m$. $\square$

(B1) Uniformly for $t\in[\delta,1/\delta]$, $x\in[\delta,1]$: $q_{m_N(t)+1}(\lfloor xN\rfloor)=T(N)[Q_t(x)+o(1)]$
(same for the minus sign with $Q^b_t$, using $T_-(N)\sim bT_+(N)$).
*Proof.* Split $r\le k-\theta N$ and $r>k-\theta N$. On the first part $T(k-r)/T(N)\to((k-r)/N)^{-\alpha}$
uniformly (UCT) and (G) turns the sum into a Riemann sum for $\int_0^{x-\theta}p_t(z)(x-z)^{-\alpha}dz$.
The second part is at most $(C/a_m)\sum_{i\le\theta N}T(i)\le C_\delta\theta^{1-\alpha}T(N)$, and the
integral over $[x-\theta,x]$ is at most $C_\delta\theta^{1-\alpha}$. Let $N\to\infty$, then $\theta\to0$. $\square$

**(B2) Key bound. Under (RV) alone, $q_{m+1}(k)\le C\,T(k)$ for all $m\ge0$, $k\ge1$.**
*Proof.* $q_1=T$. For $m\ge1$, the part $r<k/2$ is at most $T(k/2)\le CT(k)$. For $r\ge k/2$ write
$i=k-r\in(0,k/2]$ and split into dyadic blocks $i\in[w/2,w)$. On a block,
$\sum u_m(k-i)T(i)\le T(w/2)\,P(S_m\in(k-w,k-w/2])$, and
$P(S_m\in(k-w,k-w/2])\le\min\{C\,mT(k),\ C\,w\,mT(k)/a_m\}$ by (A1) and (CD1.6). Summing,
blocks with $w\le a_m$ give $C\frac{mT(k)}{a_m}\sum_{w\le a_m}wT(w/2)\le C\,mT(k)T(a_m)$ ($wT(w)$ is RV
with index $1-\alpha>0$), and blocks with $w>a_m$ give $C\,mT(k)\sum_{w>a_m}T(w/2)\le C\,mT(k)T(a_m)$.
Since $mT(a_m)\le C$ for all $m$, the total is $\le CT(k)$. (If $a_m>k/2$ only the first kind occurs.) $\square$

(B3) $q_m(j)\le C\,T(j)\,e^{-c\,mT(j)}$ for all $m\ge1$, $j\ge1$, under (RV).
*Proof.* For $m\le1/T(j)$ this is (B2). Otherwise with $h=\lfloor(m-1)/2\rfloor$,
$q_m(j)=\sum_{s<j}u_h(s)q_{m-h}(j-s)\le CT(j/2)P(S_h<j/2)+C\sup_{s<j}u_h(s)\cdot jT(j)$, and by (A2),(A3)
both terms are $\le CT(j)e^{-chT(j)}$ ($a_h\ge cj$ when $h\ge c'/T(j)$). $\square$

---

## 2. Theorem 1: the local Lamperti law

**Theorem 1.** Assume (RV$_\alpha$) and (SPAN). Let the start be fresh, of either sign. Let
$$\Lambda(x)=\int_0^\infty\bigl[p^b_t(1-x)Q_t(x)+p_t(x)Q^b_t(1-x)\bigr]dt,\qquad 0<x<1 .$$
(a) $\Lambda=L_{\alpha,b}$.
(b) The following are equivalent: (i) $NP_N(\lfloor x_0N\rfloor)\to L_{\alpha,b}(x_0)$ for one $x_0\in(0,1)$;
(ii) $NP_N(k)=L_{\alpha,b}(k/N)+o(1)$ uniformly over $k/N$ in each compact subset of $(0,1)$;
(iii) (SRT$_+$) and (SRT$_-$).
(c) Consequently (CD1.4): for $\alpha>1/2$ the local law holds under (RV$_\alpha$),(SPAN) alone; for
$\alpha\le1/2$ it holds iff $I_1^+(\delta;x)$ is a.n. for both run laws; (LB$_\pm$) suffices.

So the conjectured "iff with the Caravenna-Doney condition" is a theorem, for the occupation count,
once phrased run law by run law: the bivariate problem reduces exactly to the two univariate SRTs.

### 2.1 Decomposition

Fresh plus start, $k+j=N$, $k,j\ge1$. By the fresh-plus identity
$$P_N(k)=\underbrace{\sum_{m\ge1}u^-_m(j)\,q^+_{m+1}(k)}_{\text{Term 1}}+\underbrace{\sum_{m\ge1}u^+_m(k)\,q^-_m(j)}_{\text{Term 2}} .$$
Fix $\delta\in(0,1)$ and split $m$ into small ($m<\delta/T_+(N)$), medium, and large ($m>\delta^{-1}/T_+(N)$).
Throughout $k/N\in[x_1,x_2]\subset(0,1)$, $x=k/N$, $y=1-x$. All terms are nonnegative.

### 2.2 Medium and large $m$ (no SRT needed)

*Medium.* By (G), $u^-_m(j)=a_m^{-1}[g_b(j/a_m)+o(1)]$ uniformly, and by (B1)
$q^+_{m+1}(k)=T_+(N)[Q_t(x)+o(1)]$ with $t=mT_+(N)$. As $a_m=Nt^{1/\alpha}(1+o(1))$, the sum over medium
$m$ is a Riemann sum with mesh $T_+(N)$:
$$N\cdot\text{Term1}_{\rm med}\to\int_\delta^{1/\delta}p^b_t(y)Q_t(x)\,dt,\qquad N\cdot\text{Term2}_{\rm med}\to\int_\delta^{1/\delta}p_t(x)Q^b_t(y)\,dt,$$
uniformly in $x\in[x_1,x_2]$. Call the sum of the limits $\Lambda_\delta(x)$; $\Lambda_\delta\uparrow\Lambda$.

*Large.* By (A3) and (B2), $\text{Term1}_{\rm large}\le C\,T_+(N)\sum_{m>\delta^{-1}/T(N)}a_m^{-1}e^{-(m/2)T_-(j+1)}$.
Since $T_-(j+1)\ge cT_+(N)$, this is $\le\frac CN\int_{1/\delta}^\infty t^{-1/\alpha}e^{-ct}dt\cdot(1+o(1))$,
which is $o_\delta(1)/N$. Term 2 likewise, using (B3) or (B2).

### 2.3 Small $m$: sufficiency and necessity

*Upper bound.* By (B2), $q^+_{m+1}(k)\le CT_+(k)\le C_{x_1}T_+(N)$, and $q^-_m(j)\le C T_-(j)$. So
$$\text{Term1}_{\rm small}\le C\,T(N)\sum_{m<\delta/T(N)}u^-_m(j),\qquad \text{Term2}_{\rm small}\le C\,T(N)\sum_{m<\delta/T(N)}u^+_m(k).$$
Since $j\asymp N$ and $k\asymp N$, $NT(N)\asymp jT_-(j)\asymp kT_+(k)$ and $\delta/T(N)\le A(\delta'j)$ with
$\delta'\to0$ as $\delta\to0$. Under (SRT$_\pm$), (CD4.1) gives $\lim_\delta\limsup_N N\cdot\text{Term}_{\rm small}=0$.
With 2.2: $NP_N(k)=\Lambda(x)+o(1)$ uniformly, i.e. (iii)$\Rightarrow$(ii) (given (a)).

*Lower bound.* $q^+_{m+1}(k)\ge P(S^+_m<k/2)\,T_+(k)\ge\frac12T_+(N)$ for $m<\delta/T(N)$ and $\delta$
small, by (A1). Likewise $q^-_m(j)\ge\frac12T_-(j)$. Suppose (i). Since every term is nonnegative,
$$\tfrac12NT_+(N)\sum_{m<\delta/T(N)}u^-_m(j_N)\le NP_N(k_N)-N\,\text{Term}_{\rm med}\to L(x_0)-\Lambda_\delta(x_0)=:\varepsilon(\delta)\xrightarrow[\delta\to0]{}0,$$
with $k_N=\lfloor x_0N\rfloor$, $j_N=N-k_N$. As $N$ increases, $j_N$ increases by 0 or 1, so it takes every
large integer value; for $j=j_N$, $NT(N)\asymp jT_-(j)$ and $\delta/T(N)\ge A(\delta''j)$. Hence
$\lim_\delta\limsup_j jT_-(j)\sum_{m\le A(\delta''j)}u^-_m(j)=0$, which is (SRT$_-$) by (CD4.1). The same
argument with Term 2 and $k_N$ (which also takes every large value) gives (SRT$_+$). (ii)$\Rightarrow$(i)
is trivial. The fresh minus start differs only by the index shift $q^+_m\leftrightarrow q^+_{m+1}$, which
does not affect any limit. $\square$

### 2.4 Proof of (a): $\Lambda=L_{\alpha,b}$

*Homogeneity.* Put $\lambda(x,y)=\int_0^\infty[p^b_t(y)Q_t(x)+p_t(x)Q^b_t(y)]dt$. From
$p_t(cz)=c^{-1}p_{tc^{-\alpha}}(z)$ and $Q_t(cx)=c^{-\alpha}Q_{tc^{-\alpha}}(x)$, $\lambda(cx,cy)=c^{-1}\lambda(x,y)$, so
$\lambda(x,y)=\Lambda\bigl(\frac x{x+y}\bigr)/(x+y)$.

*Laplace transform.* $\int e^{-\mu y}p^b_t(y)dy=e^{-bt\Gamma\mu^\alpha}$ and
$\int e^{-\lambda x}Q_t(x)dx=e^{-t\Gamma\lambda^\alpha}\Gamma(1-\alpha)\lambda^{\alpha-1}$ ($\Gamma=\Gamma(1-\alpha)$).
Integrating in $t$,
$$\iint e^{-\lambda x-\mu y}\lambda(x,y)\,dx\,dy=\frac{\lambda^{\alpha-1}+b\mu^{\alpha-1}}{\lambda^\alpha+b\mu^\alpha}.$$
With $x=sv$, $y=s(1-v)$ the left side equals $\int_0^1\Lambda(v)\,dv/(\lambda v+\mu(1-v))$. Taking $\mu=1$,
$\lambda=1+\theta$:
$$\int_0^1\frac{\Lambda(v)\,dv}{1+\theta v}=\frac{(1+\theta)^{\alpha-1}+b}{(1+\theta)^\alpha+b}\qquad(\theta>-1). \tag{2.1}$$
At $\theta=0$ this shows $\int\Lambda=1$. (2.1) determines all moments, hence the law, on $[0,1]$.

*Inversion.* $G(z)=\int\Lambda(v)dv/(z-v)=z^{-1}\frac{(1-1/z)^{\alpha-1}+b}{(1-1/z)^\alpha+b}$. For $x\in(0,1)$, $z=x+i0$,
$1-1/z=w\,e^{i\pi}$ with $w=(1-x)/x$, so with $E=e^{i\pi\alpha}$,
$G=x^{-1}(b-w^{\alpha-1}E)/(b+w^\alpha E)$ and
$$-\tfrac1\pi\,\mathrm{Im}\,G(x+i0)=\frac{\sin\pi\alpha}{\pi}\,\frac{b\,w^{\alpha-1}(1+w)}{x\,(b^2+2bw^\alpha\cos\pi\alpha+w^{2\alpha})}=L_{\alpha,b}(x).$$
Both are continuous on $(0,1)$, so $\Lambda=L_{\alpha,b}$. $\square$ (A probabilistic check: the law of
$\sigma_1/(\sigma_1+\sigma'_b)$ with independent subordinator values has the transform (2.1), by
$E[\sigma e^{-s\sigma}]=\Gamma\alpha s^{\alpha-1}e^{-\Gamma s^\alpha}$. Numerically, the double integral equals $L$ at
$\alpha=1/2$ to $5\cdot10^{-14}$; Section 7.)

**Remark 2.1.** Theorem 1 contains a new derivation of Lamperti's global theorem in this setting (by
Scheffe), but only under SRT; the global theorem itself needs RV alone.

**Remark 2.2 (where the bivariate structure went).** The plan expected a bivariate local renewal
theorem for $(\sum X^+,\sum X^-)$. The proof shows that it is not needed: the key bound (B2) makes
the covering kernel uniformly $O(T(k))$ under RV alone, which decouples the two signs in the small-$m$
range, and then each sign's small-$m$ contribution is exactly the quantity in (CD4.1).

---

## 3. Theorem 2: the end layers

**Theorem 2.** Assume (RV$_\alpha$), (SPAN).
(a) For each fixed $j\ge0$, a fresh plus start has $P_N(N-j)=T_+(N)u_-(j)+o(T_+(N))$ and a fresh minus start
has $P_N(N-j)=T_+(N)u_-(j)\mathbf 1_{\{j\ge1\}}+o(T_+(N))$. Only (RV) of $T_+$ is used.
(b) Assume moreover (LB$_+$) and (SRT$_-$) (e.g. (LB$_\pm$)). Then, for a fresh start of either sign and
each $\delta>0$, uniformly in $0\le j\le(1-\delta)N$,
$$P_N(N-j)=T_+(N)\bigl[u_-(j)\,\Phi_b(j/N)+o(\omega_-(j))\bigr]\quad(\text{fresh plus}),\qquad
\Phi_b(y)=\frac{b^2(1-y)^{\alpha-1}}{b^2(1-y)^{2\alpha}+2b\cos\pi\alpha\,(1-y)^\alpha y^\alpha+y^{2\alpha}},$$
($u_-(j)\mathbf 1_{j\ge1}$ for fresh minus). $\Phi_b(0)=1$, and $\Phi_b$ is defined so that, when
$T_\pm(n)\sim c_\pm n^{-\alpha}$, the right side is $N^{-1}L_{\alpha,b}(1-j/N)(1+o(1))$ for $j\to\infty$.
(c) (Ratio form.) Under (LB$_\pm$) and $T_\pm(n)\sim c_\pm n^{-\alpha}$: for every $J_N\to\infty$,
$P_N(k)=N^{-1}L_{\alpha,b}(k/N)(1+o(1))$ uniformly over $J_N\le k\le N-J_N$.

*Proof of (a).* Final-run identity, fresh plus. First sum, term $r\le j$: $E[T_+(N-j-S^+_r);S^+_r<N-j]$.
On $S^+_r\le N/2$, $T_+(N-j-S_r)/T_+(N)\to1$ a.s. with a bounded ratio. On $S_r>N/2$, write $i=N-j-S_r$:
the part $i\le I$ is $\le I\max_{n\ge N/2-j}u^+_r(n)=o(T(N))$ (for fixed $r$, $u_r(n)\le r\max_{s\ge n/r}f(s)$
and $f(s)=T(s)-T(s+1)=o(T(s))$ by RV); the part $i>I$ is $\le T(I)P(S_r>N/2)\le CrT(I)T(N)$. Let $I\to\infty$.
Summing over $r$ gives $T_+(N)\sum_ru^-_r(j)=T_+(N)u_-(j)$. The second sum is $\le C_j\max_{r\le j}u^+_{r+1}(N-j)=o(T(N))$. $\square$

*Proof of (b).* For $\varepsilon N\le j\le(1-\delta)N$ this is Theorem 1, since by SRT
$T_+(N)u_-(j)\Phi_b(j/N)=N^{-1}L(1-j/N)(1+o(1))$ uniformly there. For bounded $j$ it is (a). It remains to
show: for every $\eta>0$ there is $\varepsilon>0$ with
$\limsup_N\sup_{j_0\le j\le\varepsilon N}|P_N(N-j)/(T_+(N)u_-(j))-1|\le\zeta(\eta)\to0$, using
$\Phi_b(y)=1+O(y^\alpha)$ and $u_-(j)\asymp1/(jT_-(j))$ for $j\ge j_0$ (SRT$_-$).

Term 1, $m\le M=\eta/T(N)$. Lower: $q^+_{m+1}(k)\ge P(S^+_m<\theta N)T_+(k)\ge(1-C\eta\theta^{-\alpha})T(N)$.
Upper: the part $r<\theta N$ is $\le T(k-\theta N)\le(1+o(1))(1-\varepsilon-\theta)^{-\alpha}T(N)$; for $r\ge\theta N$,
(D97) applies when $a_M\le\theta N$ (true if $\eta\le(\theta/2)^\alpha$), giving $u^+_m(r)\le CmT(\theta N)/(\theta N)$
and a contribution $\le C\eta\theta^{-1-\alpha}T(N)$. Take $\theta=\eta^{1/(2+2\alpha)}$: then
$q^+_{m+1}(k)=T(N)(1+O(\eta^{1/2}+\theta+\varepsilon))$, uniformly in $m\le M$.
Next $\sum_{m>M}u^-_m(j)\le\sum_{m>M}Ca_m^{-1}e^{-(m/2)T_-(j)}\le\frac C{jT_-(j)}\varphi(MT_-(j))$ with $\varphi(s)\to0$ as
$s\to\infty$, and $MT_-(j)\ge\eta\,T_-(\varepsilon N)/T_+(N)\to\infty$ as $\varepsilon\to0$ (for fixed $\eta$). So Term 1
over $m\le M$ is $T(N)u_-(j)(1+O(\zeta))$, and over $m>M$ it is $\le CT(N)\sum_{m>M}u^-_m(j)$ by (B2), which is
$o_\varepsilon(1)T(N)u_-(j)$.

Term 2. By (B3), $q^-_m(j)\le CT_-(j)e^{-cmT_-(j)}$. For $m\le c'/T(N)$, (D97) gives
$u^+_m(k)\le CmT(N)/N$, so this part is $\le CT_-(j)\frac{T(N)}N\sum_mme^{-cmT_-(j)}\le C\frac{T(N)}{NT_-(j)}$,
which is $\le C\frac jN\cdot T(N)u_-(j)\le C\varepsilon\,T(N)u_-(j)$. For $m>c'/T(N)$, $u^+_m(k)\le C/N$ and the part is
$\le\frac CNe^{-c''T_-(j)/T(N)}\le Ce^{-c''\varepsilon^{-\alpha}}T(N)u_-(j)$. $\square$

*Proof of (c).* For $j\ge J_N$, SRT and $T_\pm(n)\sim c_\pm n^{-\alpha}$ give
$T_+(N)u_-(j)=N^{-1}\frac{\sin\pi\alpha}{\pi b}(j/N)^{\alpha-1}(1+o(1))$ uniformly; multiply by $\Phi_b$. Same at the
minus end. $\square$ (Without pure power tails the slowly varying ratio $\ell(j)/\ell(N)$ stays, and (b) is
the correct form.)

**Corollary 2.3 (the global mode).** Under (LB$_\pm$), for a fresh start, every global mode of $P_N$ lies
within bounded distance of an end for all large $N$, at $N-\arg\max_j\kappa_+(j)$ or at
$\arg\max_j\kappa_-(j)$, whichever of $T_+(N)\max\kappa_+$ and $T_-(N)\max\kappa_-$ is larger (asymptotically
$\max\kappa_+$ versus $b\max\kappa_-$). *Proof.* On compacts $P_N\le C/N$; on $J\le j\le\varepsilon N$,
$P_N(N-j)\le CT(N)\omega_-(J)$; and $NT(N)\to\infty$. $\square$ So there is no golden-ratio transition
here: for $1<\alpha<2$ (Paper F, Thm D) the end atom beats the bulk only for $\alpha<\varphi$, while for
$0<\alpha<1$ the end always wins.

**Remark 2.4 (mass near the ends).** For every $\varepsilon_N\to0$, $P(A_N\le\varepsilon_NN)+P(A_N\ge N-\varepsilon_NN)\to0$, by
Lamperti's global theorem and integrability of $L$. The plan's "positive fraction of the mass" is wrong;
the layers dominate pointwise, not in mass. Numerically the mass within $\sqrt N$ of the ends at
$\alpha=0.5$ is 0.215, 0.182 at $N=1000,2000$ (Lamperti value $2\int_0^{N^{-1/2}}L$: 0.228, 0.191).

**Missing lemma for (b) under SRT alone (M0).** For $j\le\varepsilon N$:
$\sum_{i\le\theta N}T_+(i)\sum_{m\le\eta/T(N)}u^-_m(j)u^+_m(N-j-i)\le\zeta(\theta,\eta)\,T_+(N)u_-(j)$ with
$\zeta\to0$. (CD1.6) loses a factor $N/j$ here; (D97) is what closes it under (LB).

---

## 4. Theorem 3: the initial run (the Wang-Schulz-Deng-Barkai question for $0<\alpha<1$)

Initial run $(\Sigma,D)$ with $\nu_\pm(d)=P(\Sigma=\pm,D=d)$, $Q_\pm(N)=P(\Sigma=\pm,D\ge N)$, $D<\infty$ a.s.,
law fixed (independent of $N$) except in (g). $\pi_\pm=P(\Sigma=\pm)$.

**Theorem 3.** Assume (RV$_\alpha$), (SPAN), (SRT$_\pm$).

(a) (Exact defect.) Uniformly for $k/N$ in compacts of $(0,1)$,
$$NP_N(k)=L_{\alpha,b}(k/N)+\mathcal D^+_N(k)+\mathcal D^-_N(k)+o(1),$$
$$\mathcal D^+_N(k)=N\!\!\sum_{k/2\le d\le k}\!\!\nu_+(d)F^-_{N-d}(k-d),\qquad
\mathcal D^-_N(k)=N\!\!\!\sum_{(N-k)/2\le d\le N-k}\!\!\!\nu_-(d)F^+_{N-d}(k).$$
$\mathcal D^+$ is a first plus run that ends after at least half of the plus steps; the remainder is
then a fresh minus walk sitting in its own end layer.

(b) (Necessary condition.) If the local Lamperti law holds at one $x_0\in(0,1)$, then
$nT_\mp(n)\,\nu_\pm(n)\to0$, i.e. $\nu_\pm(n)=o(1/(nT(n)))$.

(c) (Sufficient condition; needs (LB$_\pm$).) If $n\nu_\pm(n)\to0$, the local Lamperti law holds uniformly on
compacts. In particular it holds for every initial run with eventually nonincreasing $\nu_\pm$.

(d) (Exact criterion; (LB$_\pm$) and $u_\pm(i)>0$ for all $i$, e.g. $f_\pm(1)>0$.) The local law holds on
compacts iff $\sup_{k\in[x_1N,x_2N]}NT(N)\sum_{0\le i\le k/2}\nu_+(k-i)\,\omega_+(i)\to0$ and the mirror condition
for $\nu_-$, for all $0<x_1<x_2<1$.

(e) (Visible in the bulk though $D<\infty$.) There are initial runs with $nT(n)\nu_+(n)\not\to0$; e.g.
$\nu_+(n_i)=c/(n_iT(n_i))$ on a sparse sequence $n_i=2^{2^i}$ (summable since $1/(nT(n))$ is RV of index
$\alpha-1<0$). Along $N$ with $\lfloor x_0N\rfloor=n_i$ the single term $d=k$ of $\mathcal D^+$ gives
$\liminf NP_N(\lfloor x_0N\rfloor)\ge L(x_0)+c\,b\,x_0^{\alpha-1}(1-x_0)^{-\alpha}>L(x_0)$. Conditions (b) and (c) are not equivalent: a cluster of $w_N=\sqrt N$ equal
point masses $T(w_N)/(NT(N))$ just below $n_i$, on a sparse sequence, satisfies (b) and violates (d).

(f) (End layer; RV of $T_+$ only.) For each fixed $j\ge0$,
$$P_N(N-j)=Q_+(N)\mathbf 1_{\{j=0\}}+T_+(N)\kappa_+(j)+\sum_{1\le m<N/2}\nu_+(N-m)\Pi^-_m(j)+o(T_+(N)),$$
$\kappa_+(j)=\pi_+u_-(j)\mathbf 1_{\{j\ge1\}}+\sum_{d=1}^j\nu_-(d)u_-(j-d)$ (as in Paper F). Hence
$P_N(N-j)/T_+(N)\to\kappa_+(j)$ for every $j\ge1$ iff
$$W^+_N:=\sum_{1\le m<N/2}\nu_+(N-m)\,T_+(m)=o(T_+(N)).$$
This holds if $n\nu_+(n)\to0$, and for every fresh start.

(g) (Scale-$N$ initial runs: aging type.) Let the law $\nu^{(N)}$ depend on $N$, with
$N\nu^{(N)}_\pm(\lfloor zN\rfloor)\to\rho_\pm(z)$ uniformly on compacts of $(0,1)$, $\rho_\pm$ continuous,
$\sup_N\sup_{d\ge\varepsilon N}N\nu^{(N)}_\pm(d)<\infty$ for each $\varepsilon$, and
$\pi^0=\lim_{\varepsilon\to0}\lim_NP(D^{(N)}<\varepsilon N)$. Then uniformly on compacts
$$NP_N(\lfloor xN\rfloor)\to\pi^0L(x)+\int_0^x\rho_+(z)\frac{L(\frac{x-z}{1-z})}{1-z}dz+\int_0^{1-x}\rho_-(z)\frac{L(\frac x{1-z})}{1-z}dz .$$

*Proof of (a).* First-run decomposition; the atoms vanish for interior $k$. Plus part, $d<\varepsilon N$: by
Theorem 1 (uniform in the horizon $N-d\ge(1-\varepsilon)N$ and in $(k-d)/(N-d)$ on a compact),
$NF^-_{N-d}(k-d)=L(k/N)+O(\varepsilon)+o(1)$ (continuity of $L$), and $P(D\ge\varepsilon N)\to0$. Plus part,
$\varepsilon N\le d<k/2$: $(k-d)/(N-d)\in[x_1/2,x_2]$, so $NF^-_{N-d}(k-d)\le C$, total $\le CP(D\ge\varepsilon N)\to0$.
What remains is $\mathcal D^+$. Same for the minus part; $\pi_++\pi_-=1$. $\square$

*Proof of (b).* The term $d=k$ of $\mathcal D^+$ is $N\nu_+(k)F^-_{N-k}(0)=N\nu_+(k)T_-(N-k)$ exactly; the term
$d=N-k$ of $\mathcal D^-$ is $N\nu_-(N-k)T_+(k)$. Both $k_N$ and $N-k_N$ run through all large integers. $\square$

*Proof of (c),(d).* By Theorem 2(b) at the minus end (signs exchanged), for $i\le k/2$ the remainder
satisfies $F^-_n(i)=T_-(n)[u_+(i)\Phi(i/n)+o(\omega_+(i))]$ with $n=N-k+i\asymp N$, $i/n\le x_2/(2-x_2)<1$, so
$\mathcal D^+_N(k)\asymp NT(N)\sum_{i\le k/2}\nu_+(k-i)(u_+(i)+o(\omega_+(i)))$. This gives (d). For (c),
$\sum_{i\le k}\omega_+(i)\le C/T_+(k)$ (Karamata, index $\alpha-1>-1$), so if $\nu_+(d)\le\epsilon/d$ for
$d\ge k/2$ the sum is $\le C\epsilon\,NT(N)/(kT(k))\le C'\epsilon$. $\square$

*Proof of (f).* As Paper F, Thm C(d): split the first-run decomposition at $d=N/2$. For $d\le N/2$ use
Theorem 2(a) uniformly in the horizon $n\in[N/2,N]$ and dominated convergence ($T(N-d)/T(N)\le C$,
$\to1$ for $d=o(N)$). For $d>N/2$ the plus part is exactly $\sum_m\nu_+(N-m)\Pi^-_m(j)$, $m=N-d$. The minus
part needs $d\le j$ and gives $T_+(N)\sum_{d\le j}\nu_-(d)u_-(j-d)$. For the criterion: by Theorem 2(a) for
a fresh minus walk, $\Pi^-_m(j)/T_+(m)\to u_-(j)\mathbf 1_{j\ge1}$, so $\Pi^-_m(j)\le C_jT_+(m)$ for all $m$, which
gives "if". Conversely, pick $j^*$ with $u_-(j^*)>0$; then $\Pi^-_m(j^*)\ge cT_+(m)$ for $m\ge m^*$, which
controls $\sum_{m\ge m^*}$; for each $m<m^*$ use $j=m$, where $\Pi^-_m(m)=T_-(m)>0$, to get
$\nu_+(N-m)=o(T(N))$. If $n\nu_+(n)\to0$, $W^+_N\le o(1/N)\sum_{m<N/2}T(m)=o(T(N))$, since
$\sum_{m<N/2}T(m)\sim NT(N)/((1-\alpha)2^{1-\alpha})$. For a fresh start, $\sum_{m<M}f(N-m)=o(T(N))$ for fixed $M$
and $\sum_{M\le m<N/2}f(N-m)T(m)\le T(M)\,T(N/2)$. $\square$

*Proof of (g) (outline).* Riemann sums with Theorem 1 on compacts; near $z=x$ the remainder is in its
end layer, where Theorem 2 gives an integrable singularity $((x-z)/(1-x))^{\alpha-1}$ and mass
$O(\theta^\alpha)$ from $|z-x|\le\theta$ (the bounded density of $\nu^{(N)}$ at scale $N$ means no spike);
near $z=0$ use $\varepsilon\to0$. Needs (LB$_\pm$) for the near-$z=x$ step as written. $\square$

**The answer, in one paragraph.** In the infinite-mean regime the initial run matters in a way it
does not for $1<\alpha<2$. In Paper F (Thm C(b)) the bulk needs no condition on any macroscopic
interior. Here it does: a first run that ends just before the $k$-th plus step leaves a remainder in
its end layer, where probabilities are of order $T(N)\gg1/N$, so $N\nu_+(k)T(N)$ survives (Thm 3(b),(e)).
For every reasonable fixed preparation ($n\nu(n)\to0$, e.g. any eventually monotone $\nu$) the local
Lamperti law and the end layers are unchanged (Thm 3(c),(f)). The end criterion changes from
$\nu_+=o(T_+)$ (finite mean) to the $T$-weighted window $W^+_N=o(T_+(N))$, because $\sum_mT(m)$ now diverges
like $NT(N)$. A preparation at scale $N$ (aging) changes the local law itself, by the explicit
mixture of Thm 3(g). The stationary start does not exist here ($s=\infty$), so there is no analogue of
Paper F's Corollary stationary; the aged start replaces it.

---

## 5. Theorem 4: the shape

**Theorem 4.** (a) For $b=1$, $L_{\alpha,1}$ has exactly one critical point (a minimum at $1/2$; U-shaped)
iff $\cos(\pi\alpha/2)\ge\alpha$, i.e. $\alpha\le\alpha_c=0.5946116441\ldots$; for $\alpha>\alpha_c$ it has exactly
three: a strict local maximum at $1/2$ and two strict minima at $x=1/(1+e^{\pm t^*})$ (W-shaped).

*Proof.* By (1.1) with $\beta=0$, $L\propto\phi(t)=(1+\cosh t)/(\cosh\alpha t+c)$, even in $t$, and $x\mapsto t$
is a decreasing bijection, so critical points correspond. $\phi'(t)$ has the sign of
$\sinh t(\cosh\alpha t+c)-\alpha\sinh\alpha t(1+\cosh t)$, which for $t>0$ has the sign of
$\chi(t)=\cosh\alpha t+c-\alpha\sinh(\alpha t)\coth(t/2)$. Write $\chi=G+c$, $G=\cosh\alpha t-\alpha\sinh\alpha t\coth(t/2)$. Then
$G'(t)=\alpha\,n(t)/(2\sinh^2(t/2))$ with $n(t)=\sinh\alpha t\cosh t-\alpha\cosh\alpha t\sinh t$, $n(0)=0$,
$n'(t)=(1-\alpha^2)\sinh\alpha t\sinh t>0$. So $G$ increases strictly on $(0,\infty)$ from $G(0+)=1-2\alpha^2$ to
$+\infty$, and $\chi$ has no zero on $(0,\infty)$ iff $1+\cos\pi\alpha-2\alpha^2\ge0$, i.e.
$2\cos^2(\pi\alpha/2)\ge2\alpha^2$; otherwise exactly one zero $t^*$. $\square$

Credit: the value $0.5946$ appears in Margolin and Barkai (J. Stat. Phys. 122 (2006) 137-167,
cond-mat/0504454); Zaburdaev-Denisov-Klafter (RMP 2015) give "about 0.6" (per the plan; not checked).
I could not extract their derivation (the PDF text is font-garbled); I did not find the closed form
$\cos(\pi\alpha/2)=\alpha$ or a proof that the count is exactly 1 or 3. For $b\ne1$ the derivative sign is
$\tanh(t/2)(\cosh(\alpha t-\beta)+c)-\alpha\sinh(\alpha t-\beta)$, which goes from $-\infty$ to $+\infty$, so the count is
odd; numerically it is 1 or 3 (e.g. $\alpha=0.7$: 3 for $b\le2$, 1 for $b=3$). Not proved for $b\ne1$.

(b) (Lower bound for the discrete law.) Assume Theorem 1's hypotheses, a fixed initial run with
$W^\pm_N=o(T_\pm(N))$ and the bulk criterion of Thm 3, and let the end profiles $\kappa_\pm$ have
$\kappa_\pm(j+1)\ne\kappa_\pm(j)$ for all $j$ and be eventually strictly decreasing (true for strictly
log-convex run laws: de Bruijn-Erdos, as in Paper F Lemma logconvex, plus $u\to0$). Let $\sigma_\pm$ be the
number of sign changes of $j\mapsto\kappa_\pm(j+1)-\kappa_\pm(j)$, and $\sigma_L$ the number of critical points of
$L_{\alpha,b}$ (assumed finite, all strict extrema). Then for all large $N$ the number of sign changes
of $k\mapsto P_N(k+1)-P_N(k)$ is at least $\sigma_L+\sigma_++\sigma_-$.

*Proof.* Sample: $J$ points at each end (Thm 3(f): $P_N(N-j)/T_+(N)\to\kappa_+(j)$, pattern copied), and
points $z_0<\dots<z_{\sigma_L+1}$ in $(0,1)$ alternating around the extrema of $L$ (Thm 1). Since $L\to\infty$ at
both ends, $L$ increases toward each end; since $\kappa_\pm$ decreases for $j\ge J$ and $T(N)\kappa(J)\gg1/N$
($NT(N)\to\infty$), the junction between the bulk samples and the end samples adds no sign change and
removes none. The number of sign changes of the differences of a sequence is at least that of any
subsequence. $\square$

**Conjecture 4.1 (exact count).** Under (LB$_\pm$), (LD$_\pm$) of Paper F, and log-convex laws, for all large
$N$ the count equals $\sigma_L+\sigma_++\sigma_-$. Missing lemmas:
(M1) a difference form of Theorem 1: $N^2[P_N(k+1)-P_N(k)]\to L'(x)$ on compacts;
(M2) a difference form of Theorem 2(b): the sign of $P_N(N-j-1)-P_N(N-j)$ is that of $u_-(j+1)-u_-(j)<0$ for
$J\le j\le\varepsilon N$, which needs a difference SRT, $u(j)-u(j+1)\sim(1-\alpha)u(j)/j$ (I did not check whether
this is in the literature for $\alpha\le1/2$).

*Explanation of the plan's counts* (symmetric zeta, fair start, so $\kappa(0)=\frac12$, $\kappa(j)=u(j)$, $j\ge1$,
$u$ strictly decreasing): $\sigma_\pm=1$ iff $f(1)=1/\zeta(1+\alpha)>\frac12$ iff $\zeta(1+\alpha)<2$; $\zeta(1.7)=2.054$,
$\zeta(1.9)=1.750$. So $\alpha=0.3,0.5$: $1+0+0$; $\alpha=0.7$: $3+0+0$; $\alpha=0.9$: $3+1+1=5$. The sign
changes at $\alpha=0.9$ sit at $k=1,\ N/2\pm0.46N\ (\text{the minima}),\ N/2,\ N-1$: computed positions
$1,142,2000,3858,3999$ at $N=4000$. The fresh plus asymmetric case ($\kappa_-(0)=0$) gives $1+0+1=2$,
as computed.

---

## 6. Literature (what was checked, exact statements, what they do not cover)

- **Lamperti 1958**, Trans. AMS 88, 380-387. Primary source not accessible (AMS 403). Restated in
  Akimoto (arXiv 0801.1382, Thm 1 and proof): for an occupation time $N_n$ of a recurrent-event
  setting, $N_n/n$ has a limit law iff $E(N_n/n)\to c$ and $(1-x)u'(x)/(1-u(x))\to\alpha$ ($u$ the generating
  function of the recurrence law); the symmetric density quoted there (Eq. 8) agrees with $L_{\alpha,1}$.
  Global, in distribution; nothing local, no end layers, no initial-run dependence. I re-derived the
  density independently (2.4), so no proof here depends on the restatement.
- **Mitov-Yanev 2001**, Adv. Appl. Probab. 33(4), 896-911, DOI 10.1239/aap/1011994035. Only the
  abstract was accessible: limit theorems for the occupation-time process of alternating renewal
  processes in the infinite-mean case, extending Dynkin, Lamperti and Erickson for the spent lifetime.
  Exact statements **not verified**. From the abstract, distributional; I found no indication of local
  results.
- **Caravenna-Doney 2019**, EJP 24, paper 72 (arXiv 1612.07635v3), read in full for what is used:
  Thm 1.1 (local large deviations, (1.4)-(1.6), RV only, $\alpha\in(0,1)\cup(1,2)$); Thm 1.4 (renewal SRT:
  automatic for $\alpha>1/2$; iff $I^+_1(\delta;x)$ a.n. for $\alpha\le1/2$); Thm 1.5 ($\alpha=1/2$); Props 1.6-1.7;
  Section 4.1 (SRT iff small-$n$ contribution a.n.). Univariate only; no occupation times.
- **Garsia-Lamperti 1962/63** (Comment. Math. Helv. 37, 221-234), **Williamson 1968**, **Erickson 1970**
  (Trans. AMS 151): SRT for $\alpha>1/2$ (as credited in CD). Not read in the original.
- **Doney 1997**, PTRF 107, 451-465: SRT and local LD bound under (LB) in the arithmetic case (as
  stated in CD Section 1.4 and Berger 2019 Thm 2.4). Not read in the original.
- **Starreveld-Bekker-Mandjes**, J. Appl. Probab. 55(4) (2018) 1287-1308 (arXiv 1602.05131), read:
  transform of the occupation time at an exponential time (Thm 3.1), CLT under finite second moments
  (Thm 3.2), large deviations under a finite cumulant generating function (Thm 3.3), reflected Levy
  application (Thm 3.4). Nothing on infinite means, nothing local.
- **Wang-Schulz-Deng-Barkai 2018** (PRE 98, 042139): per Paper F's reading, an atom with a boundary
  layer for $0<\alpha<1$ in continuous time, one law, fair start, and the preparation question left
  open (Section VIII). **Akimoto 2023** (arXiv 2306.00359): aging and generalized arcsine laws for
  alternating renewal processes, distributional.
- Searches for a local (pointwise) generalized arcsine law for discrete occupation counts found
  nothing (alphaXiv/web, terms: local limit theorem, occupation time, Lamperti, generalized arcsine,
  pointwise). Yamato (arXiv 2605.23659, May 2026) proves multiscale occupation-time limits for
  time-changed regenerative processes; from the abstract they are distributional. This is a bounded
  search, not a proof of novelty.

---

## 7. Numerics (all exact up to double-precision rounding of nonnegative sums)

Commands (from this folder):
```
py -I lamperti_exact.py      # 56 s; writes lamperti_exact_output.txt
py -I initial_run.py         # 15 s; writes initial_run_output.txt
```
Method (independent of the plan's script): bivariate renewal arrays $A=U^\top U$, $B=U_{1:}^\top U_{:-1}$ from the
convolution powers $U_{m,k}=f^{*m}(k)$, then
$F^+_N(k)=\sum_{k'<k}A(k',j)T_+(k-k')+\sum_{j'<j}B(k,j')T_-(j-j')$ (split on the run in progress). Checked against
brute force over all sign strings, $N\le12$: max difference $2.2\cdot10^{-16}$ (P3). Total mass 1 to 12 digits.

Ratio $NP_N(k)/L(k/N)$, symmetric zeta, fair start ($x=0.05,0.1,0.2,0.3,0.4,0.5$):

| $\alpha$ | $N$ | ratios | sign changes (positions) |
|---|---|---|---|
| 0.3 | 1000/2000/4000 | centre 1.0852, 1.0687, 1.0555; $x=0.05$: 1.1023, 1.0845, 1.0694 | 1, 1, 1 |
| 0.5 | 1000/2000/4000 | centre **1.0149, 1.0105, 1.0075**; $x=0.05$: 1.0045, 1.0036, 1.0028 | 1, 1, 1 |
| 0.7 | 1000/2000/4000 | centre 0.9023, 0.9159, 0.9285; $x=0.05$: 1.1202, 1.1004, 1.0833 | 3, 3, 3 (104, 500, 896 at 1000) |
| 0.9 | 1000/2000/4000 | centre 0.4903, 0.5168, 0.5433; $x=0.05$: 2.289, 2.128, 1.991 | 5, 5, 5 (1, 142, 2000, 3858, 3999 at 4000) |

These reproduce the plan's table to its three decimals (P1, P2). Near the threshold: $\alpha=0.56$ gives
1 and $\alpha=0.62$ gives 3 at all three $N$ (P5). Asymmetric check (plus zeta, minus
$f(n)\propto(n+3)^{-\alpha-1}$, $b=\zeta(\alpha+1)/\zeta(\alpha+1,4)$, fresh plus): at $\alpha=0.5$, $b=2.450$, ratios
to $L_{\alpha,b}$ at $x=0.1,\dots,0.9$ go 1.037-1.012 ($N=1000$) to 1.019-1.007 ($N=4000$); at $\alpha=0.7$, $b=3.470$,
0.846-1.299 to 0.886-1.192; counts 2 (= $1+0+1$). P4: the double integral $\Lambda$ equals $L$ at
$\alpha=1/2$ to $5\cdot10^{-14}$.

End layer (P7), $P_N(N-j)/(T(N)\kappa(j))$, $j=1..5$, at $\alpha=0.5$: 1.0009-1.0040 ($N=1000$),
1.0004-1.0020 ($N=2000$): error halves with $N$. Uniform layer (P8), $P_N(N-j)/(T(N)u(j)\Phi(j/N))$ over
$1\le j\le0.8N$ at $\alpha=0.5$: range [1.0004, 1.0148] ($N=1000$), [1.0002, 1.0105] ($N=2000$); slower for
$\alpha=0.3$ ([1.070, 1.099] at 2000) and $\alpha=0.9$ (0.31 at $j=N/2$, the bulk itself is slow there).

Initial runs, $\alpha=0.5$ (P-initial): (R) fair sign, $\nu(d)\propto d^{-1.2}$: ratio at $x=0.5$ 0.815, 0.836,
0.855 for $N=500,1000,2000$, the defect $1-$ratio decaying like $N^{-0.2}=P(D\gtrsim N)$-order, as
predicted by Thm 3(a),(c). (S) $D$ uniform on $\{1..N/2\}$: $NP_N$ at $x=0.3,0.5$: 0.898, 1.325 ($N=500$) to
0.884, 1.299 ($N=2000$) against the Thm 3(g) limits 0.869, 1.273 (fresh $L$: 0.695, 0.637). The
scale-$N$ start doubles the centre value.

Convergence is slow and degrades as $\alpha\to1$ (centre ratio at $\alpha=0.9$ is 0.54 at $N=4000$); a
second-order term would be needed for quantitative use, as the plan says. Not attempted.

---

## 8. Honest status

Proved, with cited inputs (G), (CD1.6), (CD4.1), (CD1.4), (D97): Theorem 1 entirely (including the
"iff"); Theorem 2(a); Theorem 2(b),(c) under (LB); Corollary 2.3; Theorem 3(a),(b),(f), and (c),(d) under
(LB), (e) as examples (the second example in (e) is checked only at the level of orders of magnitude), (g) in outline;
Theorem 4(a),(b). The proofs here are written at the level of a careful draft. They have not been
independently refereed. The steps most worth a second look are (B2), the necessity argument in 2.3,
and the uniformity bookkeeping in Theorem 2(b).

Not proved: Theorem 2(b) under SRT alone (missing lemma M0); the exact mode count (M1, M2); the shape
of $L_{\alpha,b}$ for $b\ne1$; a rate or second-order term.

Literature gaps: Lamperti 1958 and Mitov-Yanev 2001 not read in the original (paywalled); the
Margolin-Barkai derivation of 0.5946 not read; ZDK 2015 not checked.

Novelty (bounded search): I found no local limit theorem for the occupation count of an alternating
renewal process with infinite means. The reduction "local Lamperti law iff SRT for both laws" and the
key bound (B2) look new. The fixed-$j$ layer is routine. The initial-run criteria are new in this form.

## 9. Length estimate for a standalone paper

EJP format: introduction and results 4 pp; setting and identities (cited from F, short) 2 pp; tools
and the bound (B2) 2 pp; Theorem 1 with the inversion 6 pp; Theorem 2 4 pp; Theorem 3 5 pp; Theorem 4
3 pp; computations 1-2 pp; references 1-2 pp. About **28-32 pages**. Adding M0 (if it can be done) or
the exact mode count would add 5-10. Natural venue: EJP or AAP, given the tie to Caravenna-Doney.

## Files

- `00_predictions.md` - predictions, written before any code.
- `lamperti_exact.py`, `lamperti_exact_output.txt` - exact law, local law, shape, layers, P1-P9.
- `initial_run.py`, `initial_run_output.txt` - Theorem 3 checks.
