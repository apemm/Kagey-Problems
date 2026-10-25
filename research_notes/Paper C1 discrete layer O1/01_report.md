# The discrete boundary layer at a facet (Paper C1, item O1)

2026-10-25. Paper: `kagey-problems/problem131/paperC` at 3b3a446, read only. Plan item (O1)
of `01_C1_plan_JTP.md`; referee finding C1-F1 ("boundary layer: continuous-time density,
not the counts"). Predictions are in `00_predictions.md`, written before any code ran.

## 0. Status in one paragraph

The discrete layer is proved, for every irreducible face and every facet satisfying (H),
with the target error $O(1/T+T^2/N)$, in fact with the sharper $O(T^{-2}+x^{1/2}T^{-3/2}+T^2/N)$,
uniformly for $1\le n_i\le\delta N$ and $T_0\le T\le N^{1/2}$ (Theorem 2). Pair faces get a
stronger, fully explicit statement with no $1/T$ term and no lower bound on $T$ (Theorem 1).
The kernel carries exactly one power of $h$ for every $k$, and it is evaluated at the facet
time $S=hN'=T-x$. The route differs from the plan's in one place, and the change makes it
shorter. I never prove a discrete local law for complex weights. I discretize the facet
states with the original nonnegative weights and keep the state $i$ exact. Then the paper's
term-by-term comparison (proof of Lemma discrete) applies as it stands, and the complex
saddle analysis is needed only for the one-variable contour in $z$. One expectation in the
plan is wrong. In the range $T\le N^{1/3}$ of Theorem A the lattice kernel and the continuum
kernel at $x=hn_i$ agree up to a factor $1+O(T^2/N)$, even at $n_i=1$. So the lattice kernel
differs from the continuum kernel (and hence from its Bessel form) by more than the error
only when $T^2/N$ is of order one. For pair
faces Theorem 1 covers that regime (numerically: Laguerre error $3\cdot10^{-3}$, Bessel error
$-0.58$ at $N'=10^5$, $T=\sqrt{N'}$). For $k\ge3$ that regime is open (Section 6 below).

## 1. Notation and the lattice kernel

Section 6 of the paper sets the notation: $F$ irreducible, $|F|=k\ge2$, $i\in F$,
$G=F\setminus\{i\}$ satisfying (H), $c^-_j=q_{ji}$, $c^+_j=q_{ij}$, and the weighted facet
chain $Q_G(z)$ with $A(z)$, $d(z)$, $\mu^{(z)}$, $e^{(z)}$. Also $J_G(\beta,z)$, $C_G(\beta,z)$
and $z_0$ are as in Theorem L-facet, and $\omega_\beta$, $\gamma_\beta$, $\mathbf B_\beta$,
$\mathbf K_\beta$ as in Section 6. For a composition $n$ with support $F$ put
$$
N'=N-n_i,\qquad \hat n=n|_G,\qquad \beta=\hat n/N',\qquad S=hN',\qquad x=hn_i,\qquad
p_i=1-hq_i .
$$
So $T=S+x$ exactly, and $S$, $x$ are the parametrization of Theorem layer. Put
$$
\Lambda_\beta(z)=S^{-(k-2)/2}C_G(\beta,z)e^{-SJ_G(\beta,z)},\qquad
\widetilde\Lambda_\beta(z)=\frac{\Lambda_\beta(z)}{\Lambda_\beta(0)}=\frac{C_G(\beta,z)}{C_G(\beta,0)}e^{S(J_G(\beta)-J_G(\beta,z))},
$$
and define the **lattice kernel**
$$
\boxed{\;\mathcal L_\beta(n_i,N')=\frac h{2\pi\mathrm i}\oint_{|z|=r}\bigl(p_i+h/z\bigr)^{n_i-1}\,\widetilde\Lambda_\beta(z)\,\frac{dz}{z^2}
=\sum_{K=1}^{n_i}\binom{n_i-1}{K-1}p_i^{\,n_i-K}h^K\,[z^K]\widetilde\Lambda_\beta(z)\;}
$$
for any $0<r<2z_0$. The two forms agree because $(p_i+h/z)^{n_i-1}$ is a polynomial in $1/z$
and $\widetilde\Lambda_\beta$ is holomorphic on $|z|<2z_0$.

*Laguerre form.* Write $\widetilde\Lambda_\beta(z)=e^{S\omega_\beta z}\sum_{r\ge0}\xi_r z^r$ (so
$\xi_0=1$, $\xi_1=c_1(\beta)=\partial_z\log C_G(\beta,z)|_{z=0}$ as defined before~(layer-c1), and $\xi_r$ depends on $S$ through
$e^{S(J_G(\beta)-J_G(\beta,z)-\omega_\beta z)}$). With $B_n$ of~(refresh-polynomial),
$B_n(w)=\sum_m\binom{n-1}{m-1}w^m/m!=\frac wnL^{(1)}_{n-1}(-w)$, a direct expansion gives
$$
\mathcal L_\beta(n_i,N')=p_i^{\,n_i}\sum_{r=0}^{n_i}\xi_r\Bigl(\frac h{p_i}\Bigr)^rB^{(r)}_{n_i}(u),\qquad
u=\frac{hS\omega_\beta}{p_i}=\frac{h^2N'\omega_\beta}{p_i}.
$$
(Check: $\sum_K\binom{n-1}{K-1}p^{n-K}h^K\frac{(S\omega)^{K-r}}{(K-r)!}=p^n(h/p)^r\sum_K\binom{n-1}{K-1}\frac{u^{K-r}}{(K-r)!}=p^n(h/p)^rB_n^{(r)}(u)$.)
So the leading term is $p_i^{n_i}B_{n_i}(u)$, the vertex section's Laguerre polynomial, and
$n_iu=\omega_\beta Sx/p_i$.

*Normalization.* $P_N(n)\approx h^{k-1}f_F(s,x)$ and $P_{N'}(\hat n)\approx h^{k-2}f_G(s)$ with
$s=h\hat n$ (Lemma continuum), so the ratio of the two lattice laws is $h$ times the
continuum kernel, a density in $x$. One power of $h$ for every $k$. This answers the plan's
open point about the powers of $h$ for $k\ge3$.

## 2. Theorem 1 (pair faces: exact and explicit)

**Theorem 1.** Let $F=\{j,i\}$ with $q_{ji},q_{ij}>0$, $\mu_j>0$, put $\omega=q_{ji}q_{ij}$,
$c_0=1$, $c_1=q_{ji}+\frac{\mu_i}{\mu_j}q_{ij}$, $c_2=\frac{\mu_i}{\mu_j}\omega$, $p_l=1-hq_l$.
Let $hq_{\max}\le\frac12$, $n=(N',n_i)$ with $N',n_i\ge1$. Then:

(a) (*discrete Pedler formula*) exactly,
$$
\frac{P_N(n)}{P_{N'}(\hat n)}=R:=\sum_{K=1}^{n_i}\binom{n_i-1}{K-1}p_i^{\,n_i-K}\sum_{e=0}^2c_e\,h^e\binom{N'-1}{K-e}\Bigl(\frac{h^2\omega}{p_j}\Bigr)^{K-e},
\qquad P_{N'}(\hat n)=\mu_jp_j^{N'-1}.
$$
(b) The lattice kernel is
$\mathcal L(n_i,N')=p_i^{n_i}\bigl[B_{n_i}(u)+c_1\frac h{p_i}B'_{n_i}(u)+c_2\frac{h^2}{p_i^2}B''_{n_i}(u)\bigr]$
with $u=h^2N'\omega/p_i$.

(c) With $U=n_iu=\omega Sx/p_i$,
$$
1-\frac{U+2\sqrt U+2}{2N'}\;\le\;\frac R{\mathcal L(n_i,N')}\;\le\;\exp\bigl(2hq_j(1+2\sqrt U)\bigr).
$$
In particular, if $n_i\le N'$ and $1\le T\le N^{1/2}$, then
$R=\mathcal L\,(1+O(h+h^2\sqrt{N'n_i}))=\mathcal L\,(1+O(T/N+(T^2/N)\sqrt{n_i/N}))$. There is no
$1/T$ term and no lower bound on $T$, and the two-sided bound itself holds whenever
$hq_{\max}\le\frac12$.

(d) (*the two limits*) $\mathcal L(n_i,N')=h\mathbf K(x,S)(1+O(hS+h))$ uniformly in
$1\le n_i\le N'$ when $hS\le1$, where $\mathbf K(x,S)$ is the bracket of Proposition pair-face divided by
$\mu_je^{-q_js}$. So $\mathcal L/h\to\mathbf K$ as $n_i\to\infty$ with $x$ fixed and $hS\to0$.
For bounded $n_i$ and $hS$ of order one (that is $T\asymp\sqrt N$), the leading terms differ
by a factor in $[1-u/2,\,1-\frac u2e^{-n_iu/2}]$, which is not $1+o(1)$.

**Proof.** (a) For $G=\{j\}$ the only word in the definition of $P^{(z)}_{N'}(\hat n)$ in Lemma
layer-exact-discrete is $j^{N'}$, so
$P^{(z)}_{N'}(\hat n)=(\mu_j+zh\mu_iq_{ij})(1+zhq_{ji})(p_j+zh^2\omega)^{N'-1}$. Divide by
$P^{(0)}_{N'}=\mu_jp_j^{N'-1}$, expand $(1+zh\frac{\mu_i}{\mu_j}q_{ij})(1+zhq_{ji})=\sum_ec_eh^ez^e$
and $(1+zh^2\omega/p_j)^{N'-1}$ by the binomial theorem, and insert in the lemma.

(b) $[z^K]\widetilde\Lambda$ for $\widetilde\Lambda(z)=(1+z\frac{\mu_i}{\mu_j}q_{ij})(1+zq_{ji})e^{S\omega z}$
(Lemma L-two, $\varepsilon=0$) is $\sum_ec_e(S\omega)^{K-e}/(K-e)!$; then use the Laguerre form
of Section 1 with $\xi_e=c_e$.

(c) Term by term, with $m=K-e$, the $(K,e)$ term of $R$ is $\rho_m$ times the $(K,e)$ term
$t_{K,e}=\binom{n_i-1}{K-1}p_i^{n_i-K}h^Kc_e(S\omega)^m/m!$ of $\mathcal L$, where
$$
\rho_m=\frac{h^{e+2m}\binom{N'-1}{m}p_j^{-m}}{h^{K+m}N'^m/m!}=\prod_{l=1}^m\Bigl(1-\frac l{N'}\Bigr)\cdot p_j^{-m}
$$
($\rho_m=0$ for $m\ge N'$). All $t_{K,e}\ge0$, so $R/\mathcal L=\mathbb E_\nu\rho_m$ for the
probability $\nu\propto t_{K,e}$. Since the factors $1-l/N'$ lie in $[0,1]$ and
$-\log(1-y)\le2y$ for $y\le\frac12$,
$1-\frac{m(m+1)}{2N'}\le\rho_m\le e^{2hq_jm}$. It remains to bound two averages. Fix $e$ and
write $t_{K,e}\propto\beta_K=\binom{n_i-1}{K-1}u^{K-e}/(K-e)!$ (the factor $p_i^{n_i}(h/p_i)^e$
does not depend on $K$). Then
$\beta_{K+1}/\beta_K=\frac{n_i-K}K\cdot\frac u{K+1-e}\le\frac U{K(K+1-e)}$. Multiplying
$\beta_{K+1}K(K+1-e)\le U\beta_K$ out and summing over $K$ gives, under the law
$\propto\beta_K$: $\mathbb E[(m-1)m]\le U$ for $e=0$ (where $m\ge1$), $\mathbb E[m^2]\le U$ for
$e=1$, and $\mathbb E[m(m+1)]\le U$ for $e=2$. Hence $\mathbb E[m]\le1+\sqrt U$ in all three
cases, $\mathbb E[m(m+1)]\le U+2\sqrt U+2$, and the lower bound follows. For the upper bound,
let $\mathcal S_e(u)=\sum_K\beta_K(u)$. Since $\beta_K\propto u^m$,
$\frac d{du}\log\mathcal S_e(u)=\mathbb E^{(u)}[m]/u$, so with $\sigma=e^c$, $c=2hq_j\le1$,
$$
\log\mathbb E\,e^{cm}=\log\frac{\mathcal S_e(\sigma u)}{\mathcal S_e(u)}=\int_u^{\sigma u}\frac{\mathbb E^{(v)}[m]}v\,dv\le c\,(1+\sqrt{\sigma U})\le c(1+2\sqrt U).
$$
Mixing over $e$ keeps both bounds. For the last claim, $U/N'=\omega h^2n_i/p_i$,
$\sqrt U/N'\le h\sqrt{2\omega}$ when $n_i\le N'$, $1/N'\le2h$, and
$hq_j\sqrt U=O(h^2\sqrt{N'n_i})$.

(d) Write $n=n_i$, $p=p_i$ and $a_K=[z^K]\widetilde\Lambda=\sum_ec_e(S\omega)^{K-e}/(K-e)!\ge0$.
The $(K,e)$ terms of $\mathcal L/h$ and of $\mathbf K(x,S)=e^{-q_ix}\sum_K\frac{x^{K-1}}{(K-1)!}a_K$
have the ratio $\prod_{1\le l<K}(1-l/n)\cdot p^{n-K}e^{hq_in}$, which lies in
$[(1-\frac{K(K-1)}{2n})e^{-2hq_i^2x},\,e^{hq_iK}]$. So it suffices to bound
$\mathbb E_\nu[K(K-1)]/(2n)$ and $\mathbb E_\nu e^{hq_iK}-1$ for the probability $\nu$ of (c), in the
notation of (c). For $e=0$: $\mathbb E_0[K(K-1)]=\mathbb E_0[(m-1)m]\le U$, which contributes
$U/(2n)=u/2=O(hS)$. For $e=1$: $m=K-1$ and $\mathbb E_1[m]\le\mathbb E_1[m^2]\le U$, so
$\mathbb E_1[K(K-1)]\le2U$. For $e=2$: $\mathbb E_2[K(K-1)]=\mathbb E_2[(m+2)(m+1)]\le3U+2$. The constant
$2$ comes with the weight $\nu(e=2)/\nu(e=0)=c_2(h/p)^2B_n''(u)/B_n(u)=c_2(h/p)^2\mathbb E_0[m(m-1)]/u^2\le c_2nh/(pS\omega)$,
so it contributes $O(h/S)$. Hence $\mathbb E_\nu[K(K-1)]/(2n)=O(hS+h/S)$. Also
$\mathbb E_\nu[K]\le2+\sqrt U$, and the argument of (c) gives
$\mathbb E_\nu e^{hq_iK}-1=O(h(1+\sqrt U))=O(h+hS)$, because $U\le2\omega Sx\le2\omega S^2$ for $n\le N'$.
For the second claim, the leading term of $\mathcal L$ is $p^{n}B_{n}(u)$, and that of $h\mathbf K$ is
$hz_*^{-1}I_1(\zeta)e^{-q_ix}=p^nu\,\mathcal I(nu)(1+O(hS+h))$, with $\mathcal I$ of Section 8 (near a vertex). By the
proof of Lemma uniform-laguerre-bessel,
$u\mathcal I(au)-B_a(u)=u\sum_{j\ge1}[1-\prod_{l\le j}(1-l/a)]\frac{(au)^j}{j!(j+1)!}$. Every
bracket lies in $[0,1]$, and the term $j=1$ alone is $u^2/2$. With $\mathcal I(y)\le e^{y/2}$ this
gives $\frac u2e^{-au/2}\le1-B_a(u)/(u\mathcal I(au))\le\frac u2$ for every $a\ge1$. $\square$

## 3. Theorem 2 (every facet)

**Theorem 2.** Let $F$ be irreducible, $k=|F|\ge2$, $i\in F$, $G=F\setminus\{i\}$ satisfying
(H), and $\mathcal K\subset\Delta_G^\circ$ compact. There are $\delta>0$, $T_0$, $\varepsilon_1>0$
and $C$ such that, uniformly for $n$ with support $F$, $\beta=\hat n/N'\in\mathcal K$,
$1\le n_i\le\delta N$ and $T_0\le T\le N^{1/2}$ (so $hq_{\max}\le\frac12$ for $N$ large):

(a) $P_N(n)=P_{N'}(\hat n)\,\mathcal L_\beta(n_i,N')\,(1+E)$ with
$$
|E|\le C\Bigl(\frac1{T^2}+\frac{x^{1/2}}{T^{3/2}}+\frac{T^2}N\Bigr)\le C'\Bigl(\frac1T+\frac{T^2}N\Bigr).
$$
(b) If also $T\le\varepsilon_1N^{1/2}$, then $\mathcal L_\beta(n_i,N')=h\,\mathbf K_\beta(x',S)(1+O(T^2/N))$
for $x'=hn_i$ and for $x'=h(n_i-1)$ (with $\mathbf K_\beta(0,S)=[z]\widetilde\Lambda_\beta=S\omega_\beta+c_1(\beta)$).
Hence
$$
P_N(n)=P_{N'}(\hat n)\,h\,\mathbf K_\beta(hn_i,S)\Bigl(1+O\Bigl(\frac1T+\frac{T^2}N\Bigr)\Bigr).
$$
(c) (*Bessel forms for the counts*) Under (b), with $x=hn_i$,
$P_N(n)=P_{N'}(\hat n)\,h\,\mathbf B_\beta(x,S)\,e^{E}$ with
$|E|\le C(1/T+T^2/N+\sqrt{x/T}(1+x))$; and if $Q$ is reversible on $F$ (or, by finding C1-F6,
$\pi^{\rm in}_\beta=\pi^{\rm out}_\beta$ wherever the paper's proof of (c) uses only that),
$P_N(n)=P_{N'}(\hat n)\,h\,\mathbf B_\beta(x,S)\bigl(1+c_1(\beta)z_*\frac{I_0(\zeta)}{I_1(\zeta)}+E'\bigr)$ with
$|E'|\le C((1+x)/T+T^2/N)$.

For $k=2$, Theorem 1 replaces (a) by an exact statement.

The rest of this section proves Theorem 2. Constants depend only on $Q,\mu,i,\mathcal K$. Write
$n=n_i$, $p=p_i$, $s=h\hat n=S\beta$, $\tilde x=(n-1)h$, and
$$
w_d(z)=(p+h/z)^{n-1}=\sum_{K=1}^{n}b_Kz^{-(K-1)},\qquad b_K=\binom{n-1}{K-1}p^{n-K}h^{K-1}\ge0 .
$$

### 3.1 Lemma D (the runs in $i$, coefficient form)

*For any nonnegative rates $q'$ on $F$ with zero diagonal, any start $\mu$, any $q_G\in\R^G$
used only in the exponent, and $s\in(0,\infty)^G$, $K\ge1$:*
$$
e^{-\langle q_G,s\rangle}\sum_{m\in\Z^F_{\ge1},\,m_i=K}W'(m)\prod_{j\in G}\frac{s_j^{m_j-1}}{(m_j-1)!}=[z^K]f'^{(z)}_G(s),
$$
*where $W'$ is $W$ of Section 2 for $q'$ and $f'^{(z)}_G$ is $f^{(z)}_G$ of Lemma layer-exact built
from $q'$ (with $A'(z)$, $\mu'^{(z)}$, $e'^{(z)}$, and $d'(z)=q_G-zc'^-\circ c'^+$).*

*Proof.* This is the content of the proof of Lemma layer-exact before the last step. That
proof regroups the words $c$ with $K$ letters $i$, and the factor $x^{K-1}/(K-1)!$ separates.
It uses the rates only as weights, so the regrouping holds for any nonnegative $q'$, and
comparing the coefficients of $x^{K-1}$ gives the identity. $\square$

### 3.2 Lemma C (the discrete contour in $z$)

Let $\varepsilon(z)=f^{(z)}_G(s)/\Lambda_\beta(z)-1$. By Theorem L-facet, $|\varepsilon|\le C/S$ on
$|z|\le z_0$. Also $\varepsilon$ is holomorphic there, since $C_G(\beta,z)\ne0$ (Step 1(ii) and
Step 4 of the proof of Theorem L-facet), and $\varepsilon\equiv0$ for $|G|=1$. By the Schwarz
lemma applied to $(\varepsilon(z)-\varepsilon(0))S/(2C)$ on $|z|<z_0$,
$$
|\varepsilon(z)-\varepsilon(0)|\le\frac{2C}{z_0}\,\frac{|z|}S\qquad(|z|\le z_0).\tag{3.1}
$$
As in the proof of Theorem layer(a), write $\widetilde\Lambda_\beta(z)=e^{S\omega_\beta z}\Xi(z)$ and
$R=\log\Xi$. After shrinking $z_0$, $R$ is holomorphic on $|z|\le z_0$, real on the real axis,
$|R(z)|\le C(|z|+S|z|^2)$, $|R'(z)|\le C(1+S|z|)$ and $|R''|\le C(1+S)$.

Put $\tilde z_*=\sqrt{\tilde x/(\omega_\beta S)}$, $\tilde\zeta=2\sqrt{\omega_\beta S\tilde x}$ and
choose the radius $\rho$ as follows. *Few visits* ($\tilde\zeta\le Z_0$):
$\rho=\max(\tilde z_*,1/S)$. *Many visits* ($\tilde\zeta>Z_0$): $\rho=\rho_d$, the critical point of
$\lambda_d(z)=(n-1)\log(p+h/z)+S\omega_\beta z+R(z)$ on $[\tilde z_*/2,2\tilde z_*]$ (shown
below to exist). Let
$\mathcal A_d=\frac1{2\pi\mathrm i}\oint_{|z|=\rho}w_d\Lambda_\beta\,\frac{dz}{z^2}$, and let
$\mathcal A_d^{\rm abs}$ be the integral of $|w_d\Lambda_\beta||z|^{-2}$ against $|dz|/2\pi$.
Put $\zeta_d=\max(1,S\omega_\beta\rho)$.

**Lemma C.** *For $Z_0$ large, then $\delta$ small and $T_0$ large: $\rho\le z_0/2$, $\mathcal A_d$ is
real and positive, $\mathcal A_d^{\rm abs}\le C\mathcal A_d$, and*
$$
\mathcal A_d\ge c\,\rho^{-1}w_d(\rho)\Lambda_\beta(\rho)\,\zeta_d^{-1/2}.\tag{3.2}
$$
*Consequently, with $\mathbf D=\frac1{2\pi\mathrm i}\oint w_d(z)f^{(z)}_G(s)\frac{dz}{z^2}$,*
$$
\mathbf D=(1+\varepsilon(0))\,\mathcal A_d\,\bigl(1+O(\rho/S)\bigr),\qquad \rho/S\le C\bigl(S^{-2}+\tilde x^{1/2}S^{-3/2}\bigr).\tag{3.3}
$$

*Proof.* Throughout, $hS\le hT=T^2/N\le1$, $\tilde x\le x\le\delta N h=\delta T$ and $S\ge(1-\delta)T$.

*Few visits.* Here $\rho\le\max(Z_0/(2\omega_{\min}),1)/S\le C/S$. On $|z|=\rho$:
$|w_d(z)|\le(p+h/\rho)^{n-1}\le e^{\tilde x/\rho}\le e^{\tilde\zeta/2}\le e^{Z_0/2}$ (since
$\tilde x/\rho\le\tilde x/\tilde z_*=\tilde\zeta/2$; for $n=1$, $w_d\equiv1$), $|e^{S\omega z}|\le C$,
and $|\Xi-1|\le C/S$. Let $\mathcal A_{d,0}$ be $\mathcal A_d$ with $\Xi=1$. Then
$\mathcal A_{d,0}/\Lambda(0)=\sum_Kb_K(S\omega)^K/K!\ge b_1S\omega=p^{n-1}S\omega\ge e^{-2q_i\tilde x}S\omega\ge cS$,
because all terms are nonnegative and $\tilde x\le Z_0^2/(4\omega_{\min}S)$. Also
$|\mathcal A_d-\mathcal A_{d,0}|\le C\Lambda(0)\rho^{-1}/S\le C\Lambda(0)$ and
$\mathcal A_d^{\rm abs}\le C\Lambda(0)\rho^{-1}\le C\Lambda(0)S$. So $\mathcal A_d\ge c\Lambda(0)S$ and
$\mathcal A_d^{\rm abs}\le C\mathcal A_d$ for $S$ large. Finally
$\rho^{-1}w_d(\rho)\Lambda(\rho)\le S\,e^{Z_0/2}\,C\Lambda(0)$, which gives (3.2).

*Many visits.* Put $a=h/\tilde z_*=h\sqrt{\omega S/\tilde x}=2h\omega S/\tilde\zeta\le2\omega_{\max}/Z_0\le\frac18$
for $Z_0\ge16\omega_{\max}$. This is the only place where the lattice enters, and it is harmless
because $hS\le1$. On $I=[\tilde z_*/2,2\tilde z_*]$,
$\lambda_d'(z)=-\frac{\tilde x}{z^2(p+h/z)}+S\omega+R'(z)$. At $\tilde z_*/2$ the first term is at
most $-4\omega S/(1+2a)$, and at $2\tilde z_*$ it is at least $-\omega S/(4p)\ge-\omega S/2$ (as
$p\ge\frac12$). With $|R'|\le C(1+S\tilde z_*)$ and $\tilde z_*\le\sqrt{2\delta/\omega_{\min}}$ small,
$\lambda_d'$ is negative at the left end and positive at the right end. Also
$\lambda_d''(z)=\tilde x\frac{2p+h/z}{z^3(p+h/z)^2}+R''(z)\ge\frac{4\tilde x}{9z^3}-C(1+S)\ge\frac{\omega S}{18\tilde z_*}-C(1+S)>0$
on $I$. So there is exactly one critical point $\rho_d\in I$, and $\rho_d\le2\tilde z_*\le z_0/2$
for $\delta$ small. On the circle, $a'=h/\rho_d\le2a\le\frac14$ and $p\ge\frac12$, so
$\operatorname{Re}(p+h/z)\ge\frac14$ and the principal logarithm makes $\lambda_d$ holomorphic near
the circle. Also $e^{\lambda_d(z)}=w_d(z)\Lambda(z)/\Lambda(0)$, and $\lambda_d$ is real on
$(0,z_0]$ because $\Lambda$ is real and positive there. Hence
$$
\mathcal A_d=\Lambda(0)\rho^{-1}\frac1{2\pi}\int_{-\pi}^{\pi}e^{\lambda_d(\rho e^{\mathrm i\phi})}e^{-\mathrm i\phi}\,d\phi .
$$
*Gap.* $|p+a'e^{-\mathrm i\phi}|^2=(p+a')^2-2pa'(1-\cos\phi)$, so the real part of the first term
of $\lambda_d$ is largest at $\phi=0$. As in the paper,
$\operatorname{Re}[R(z)-R(\rho)]\le C(\rho+S\rho^2)(1-\cos\phi)$. So
$\operatorname{Re}\lambda_d(\rho e^{\mathrm i\phi})-\lambda_d(\rho)\le-(S\omega\rho-C\rho-CS\rho^2)(1-\cos\phi)\le-\frac{\zeta_d}2(1-\cos\phi)$
for $S$ large and $\rho$ small. This gives
$\mathcal A_d^{\rm abs}\le C\Lambda(0)\rho^{-1}e^{\lambda_d(\rho)}\zeta_d^{-1/2}$, with
$\zeta_d=S\omega\rho_d\ge\tilde\zeta/4\ge Z_0/4$.

*Laplace.* Let $\ell(\phi)=\lambda_d(\rho e^{\mathrm i\phi})/\zeta_d$. Then $\ell(0)$ is real and
$\ell'(0)=0$. The critical equation reads $\frac{\tilde x}{\rho(p\rho+h)}=S\omega+R'(\rho)=S\omega(1+\eta)$
with $|\eta|\le\frac1{10}$, so $\frac{(n-1)a'}{p}=\frac{\tilde x}{p\rho}\le3\zeta_d$. The $\phi$-derivatives
of order $k\ge1$ of $\log(1+(a'/p)e^{-\mathrm i\phi})$ are $O_k(a'/p)$ since $a'/p\le\frac12$. Those of
$S\omega\rho e^{\mathrm i\phi}$ are at most $\zeta_d$, and those of $R(\rho e^{\mathrm i\phi})$ are
$O(\rho+S\rho^2)=O(\zeta_d)$. So the derivatives of $\ell$ up to order four are bounded uniformly. Also
$-\ell''(0)=\rho^2\lambda_d''(\rho)/\zeta_d$, and
$\rho^2\lambda_d''(\rho)=S\omega\rho(1+\eta)\frac{2p\rho+h}{p\rho+h}+O((1+S)\rho^2)$, with
$\frac{2p\rho+h}{p\rho+h}\in[1,2]$. So $-\ell''(0)\in[0.4,3]$. The uniform Laplace lemma
(Remark laplace-uniform, $m=1$, amplitude $e^{-\mathrm i\phi}$, $\zeta_d$ in place of $T$) gives
$\mathcal A_d=\Lambda(0)\rho^{-1}e^{\lambda_d(\rho)}(2\pi\zeta_d(-\ell''(0)))^{-1/2}(1+O(1/\zeta_d))$,
which is positive, at least $c\mathcal A_d^{\rm abs}$, and is (3.2) because
$\Lambda(0)e^{\lambda_d(\rho)}=w_d(\rho)\Lambda(\rho)$.

*Consequence.* By (3.1),
$\mathbf D=(1+\varepsilon(0))\mathcal A_d+\mathcal D'$ with
$|\mathcal D'|\le\sup_{|z|=\rho}|\varepsilon(z)-\varepsilon(0)|\,\mathcal A_d^{\rm abs}\le C(\rho/S)\mathcal A_d$.
In the few-visit case $\rho\le C/S$. In the many-visit case $\rho\le2\tilde z_*=2\sqrt{\tilde x/(\omega S)}$.
This gives (3.3). $\square$

### 3.3 Lemma B (discretizing the facet states only)

**Lemma B.** *Uniformly as in Theorem 2, $P_N(n)=h^{k-1}\,\mathbf D\,(1+O(T^2/N))$, where*
$\mathbf D=\sum_{K=1}^nb_K[z^K]f^{(z)}_G(s)$ *is the quantity of Lemma C.*

*Proof.* *Step 1 (the comparison).* By Lemma runs, $P_N(n)=\sum_mu_m$ with
$u_m=W(m)h^{M-1}\prod_{l\in F}\binom{n_l-1}{m_l-1}(1-hq_l)^{n_l-m_l}$. Since
$M-1=m_i+(k-2)+\sum_{j\in G}(m_j-1)$ and
$h^{m_j-1}\binom{n_j-1}{m_j-1}=\frac{s_j^{m_j-1}}{(m_j-1)!}\prod_{1\le l<m_j}(1-l/n_j)$, we get
$u_m=\kappa_mv_m$ with
$$
v_m=W(m)\,h^{k-2}h^{m_i}\binom{n-1}{m_i-1}p^{\,n-m_i}\prod_{j\in G}e^{-q_js_j}\frac{s_j^{m_j-1}}{(m_j-1)!}\ \ge0,\qquad
\kappa_m=\prod_{j\in G}\Bigl[\prod_{1\le l<m_j}\Bigl(1-\frac l{n_j}\Bigr)\Bigr](1-hq_j)^{n_j-m_j}e^{hq_jn_j}.
$$
The state $i$ is untouched. By Lemma D (with $q'=q$), $\sum_mv_m=h^{k-1}\sum_Kb_K[z^K]f^{(z)}_G(s)=h^{k-1}\mathbf D$,
and $\mathbf D>0$ by Lemma C. So $P_N(n)/(h^{k-1}\mathbf D)=\mathbb E_w\kappa_m$ for the probability
$w\propto v_m$. With $M_G=\sum_{j\in G}m_j$ and $n^G_{\min}=\min_{j\in G}n_j\ge\varepsilon_{\mathcal K}N'\ge\varepsilon_{\mathcal K}N/2$,
the argument for~(A-kappa) gives, word for word with $G$ in place of $F$,
$$
\Bigl(1-\frac{M_G^2}{2n^G_{\min}}\Bigr)e^{-q_{\max}^2T^2/N}\le\kappa_m\le e^{hq_{\max}M_G}.
$$
*Step 2 (the number of facet runs).* Let $\sigma=e$ and $q'$ be $q$ with the rates out of every
state of $G$ multiplied by $\sigma$ (those out of $i$ unchanged, $\mu$ unchanged). A word with $M_G$
letters in $G$ has at least $M_G-1$ jumps out of $G$-letters, so $W'(m)\ge\sigma^{M_G-1}W(m)$. Let
$v'_m$ be $v_m$ with $W'$ (same exponents $e^{-q_js_j}$). Then
$\mathbb E_w\sigma^{M_G-1}\le\sum v'_m/\sum v_m=\mathbf D'/\mathbf D$, where by Lemma D
$\mathbf D'=\sum_Kb_K[z^K]f'^{(z)}_G(s)$ and $f'$ is built from $A'(z)=\sigma A(z)$,
$\mu'^{(z)}=\mu^{(z)}$, $e'^{(z)}=\ones+z\sigma c^-$ and $d'(z)=q_G-z\sigma c^-\circ c^+$. All coefficients
are nonnegative, so $[z^K]f'^{(z)}_G(s)\le\rho^{-K}f'^{(\rho)}_G(s)$ and
$\mathbf D'\le\rho^{-1}w_d(\rho)f'^{(\rho)}_G(s)$, with $\rho$ the radius of Lemma C.

*Claim:* $f'^{(r)}_G(S\beta)\le CS^{(k-2)/2}e^{CS}\Lambda_\beta(r)$ for $\beta\in\mathcal K$, real
$0\le r\le z_0$ and $S\ge1$. For $|G|=1$ this follows from the explicit formulas:
$f'^{(r)}=(\mu_j+r\mu_iq_{ij})(1+r\sigma q_{ji})e^{-(q_j-r\sigma\omega)S}\le\sigma e^{(\sigma-1)r\omega S}\Lambda(r)$.
For $|G|\ge2$ we use Lemma torus-complex with the nonnegative weights $(\sigma A(r),\mu^{(r)},e'^{(r)})$,
which dominate themselves, at the radii $s'=\sigma\theta'(\beta,r)$. These are admissible because
$\varrho(\sigma A'(r)-\sigma\operatorname{diag}\theta'(\beta,r))=\sigma\varrho(A'(r)-\operatorname{diag}\theta'(\beta,r))<0$
by Lemma critical(a),(c),(e) ($\theta'(\beta,r)=\zeta'(\beta,r)$ is within $B_0r\le3r_0$ of $\theta'(\beta)$).
The integrand of the torus formula has modulus at most its value at $\varphi=0$, so
$H(t)\le\bar b(s')\prod_{j\ge2}s'_j\exp(t_1\bar g(s')+\sum_{j\ge2}t_js'_j)$. Scaling gives
$X_{\sigma A}(\sigma z')=\sigma^{-1}X_A(z')$, hence $\bar g(\sigma\theta')=\sigma g_{A(r)}(\theta'(\beta,r))=\sigma\theta_1(\beta,r)$
by~(A-radii) for the weights $A(r)$ (Lemma local-general), and
$\bar b(\sigma\theta')\le\sigma\,b_r(\theta'(\beta,r))\le\sigma B_0$ by Lemma critical(b), since
$e'^{(r)}\le\sigma e^{(r)}$. So
$f'^{(r)}_G(S\beta)\le C\exp(S[\sigma\langle\beta,\theta(\beta,r)\rangle-\langle\beta,d'(r)\rangle])$, while
$\Lambda(r)=S^{-(k-2)/2}C_G(\beta,r)e^{-S\langle\beta,d(r)-\theta(\beta,r)\rangle}$ by Step 4 of the proof of
Theorem L-facet, with $C_G(\beta,r)\ge c>0$ on $\mathcal K\times[0,z_0]$. Since
$d'(r)=d(r)-(\sigma-1)rc^-\circ c^+$ and $\theta(\beta,r)$ is bounded, the claim follows.

With (3.2) (and $\mathbf D\ge\frac12\mathcal A_d$ from (3.3)),
$\mathbf D'/\mathbf D\le C\zeta_d^{1/2}S^{(k-2)/2}e^{CS}\le e^{C'T}$. So
$\Upsilon(c)=\log\mathbb E_we^{c(M_G-1)}$ is convex with $\Upsilon(0)=0$ and $\Upsilon(1)\le C'T$.

*Step 3 (conclusion).* Exactly as in Step 4 of the proof of Lemma discrete:
$\mathbb E_we^{hq_{\max}M_G}\le e^{hq_{\max}(1+C'T)}=1+O(T^2/N)$, and the Chernoff bound gives
$\mathbb E_wM_G^2\le C(T^2+1)$. So $\mathbb E_w\kappa_m=1+O(T^2/N)$, since $n^G_{\min}\ge\varepsilon_{\mathcal K}N/2$. $\square$

### 3.4 Proof of Theorem 2

*(a)* By Lemma B, then (3.3),
$P_N(n)=h^{k-1}(1+\varepsilon(0))\mathcal A_d(1+O(\rho/S+T^2/N))$. By Lemma discrete for the face $G$
($N'$ steps, the same $h$, time $hN'=S$, and $S^2/N'=T^2N'/N^2\le T^2/N$), or by~(vertexmax) if
$|G|=1$, $P_{N'}(\hat n)=h^{k-2}f_G(s)(1+O(T^2/N))$. Also $f_G(s)=f^{(0)}_G(s)=\Lambda(0)(1+\varepsilon(0))$.
By definition $\mathcal L_\beta(n,N')=h\mathcal A_d/\Lambda(0)$, since the radius $\rho\le z_0/2$ is
allowed. Dividing, the factor $1+\varepsilon(0)$ cancels, and
$E=O(\rho/S+T^2/N)$, which is the bound in (a) by (3.3), $\tilde x\le x$ and $S\ge T/2$.

*(b)* Fix $x'\in\{hn,h(n-1)\}$ and let $\rho$ be the radius used for $x'$ in the proof of Theorem
layer(a): $\max(z_*,1/S)$ with few visits, $\rho_s\in[z_*/2,2z_*]$ with many, where
$z_*=\sqrt{x'/(\omega S)}$. That proof shows $\mathcal A>0$ and $\mathcal A^{\rm abs}\le C\mathcal A$
for $\mathcal A=\frac1{2\pi\mathrm i}\oint e^{x'/z}\Lambda\frac{dz}{z^2}$. For $n=1$ and $x'=0$
there is nothing to prove, since $w_d\equiv1$. On the circle put $y=h/z-hq_i$. Then
$|h/z|\le h/\rho\le\max(hS,4h\omega S/Z_0)\le CT^2/N$, so $|y|\le\frac12$ once $\varepsilon_1$ is small,
and
$$
w_d(z)=e^{(n-1)y}e^{(n-1)(\log(1+y)-y)},\qquad (n-1)|y|^2\le2h\tilde x/\rho^2+2hq_i^2\tilde x\le C\,hS+C\,hx\le C\,T^2/N,
$$
using $\tilde x/\rho^2\le4\omega S$. For $x'=h(n-1)$, $e^{(n-1)y}=e^{x'/z-q_ix'}$. For $x'=hn$ one
more factor $e^{-y}=1+O(T^2/N)$ appears. So $w_d=e^{x'/z-q_ix'}(1+\eta)$ with
$\sup|\eta|\le CT^2/N$, and
$|\mathcal A_d-e^{-q_ix'}\mathcal A|\le CT^2/N\cdot e^{-q_ix'}\mathcal A^{\rm abs}\le C'T^2/N\cdot e^{-q_ix'}\mathcal A$.
Since $\mathbf K_\beta(x',S)=e^{-q_ix'}\mathcal A/\Lambda(0)$, this is (b). The displayed consequence
combines (a) and (b).

*(c)* The proofs of Theorem layer(b),(c) are statements about $\mathbf K_\beta$ against $\mathbf B_\beta$
at the same $(x,S)$ with $S=T-x$ and $0<x\le\delta T$: $\mathbf K=\mathbf B(1+O(1/T+\sqrt{x/T}))$ for
$x\le1$, $\mathbf K=\mathbf Be^{O(\sqrt{x/T}(1+x))}$ for $1\le x\le\delta T$, and in the reversible case
$\mathbf K=\mathbf B(1+c_1z_*I_0/I_1+O(x/T))$. Combine with (b). $\square$

## 4. Paper labels used

Lemma runs, Lemma continuum, eq. (vertexmax), Lemma discrete and its proof (Steps 1 to 4, eq.
(A-kappa)), Lemma layer-exact (its regrouping), Lemma layer-exact-discrete,
Proposition pair-face and eq. (layer-bessel-moments), Proposition layer-constants(ii)
(through the expansion of $R$), eq. (layer-c1), Theorem L-facet with Lemma L-two, Lemma critical
(a),(b),(c),(e), Step 1(ii) and Step 4 of its proof, Lemma torus, Lemma torus-complex, Lemma
local-general and eq. (A-radii), Lemma laplace with Remark laplace-uniform, Theorem layer and the
proofs of (a), (b), (c), eq. (refresh-polynomial), Lemma uniform-laguerre-bessel. Nothing in the
paper is changed. The new ingredients are Lemma D (a restatement), Lemma C (the discrete contour),
Lemma B (half-discretization), the Schwarz-lemma sharpening (3.1), and Theorem 1(c),(d).

*Side remark for the paper.* (3.1) improves Theorem layer(a) itself. In its proof the error
$\varepsilon(z)$ enters only through $\varepsilon(z)-\varepsilon(0)$ once one divides by $f_G(s)$ instead of
$\Lambda(0)$. So $|E|\le C(T^{-2}+x^{1/2}T^{-3/2})$ there as well. This is consistent with the data
below, where the error at fixed $T$ tends to about $0$ as $N\to\infty$ for small $x$.

## 5. Numerics

All scripts are in this folder, LF, with a header, run with `py -I`. Outputs are saved next to
them.

| Command | What it checks | Output |
|---|---|---|
| `py -I check_exact.py` (1 s) | recursion vs brute force ($N=8$); Lemma layer-exact-discrete vs recursion for the pair face, the 3-cycle (facet of 2 states) and a 4-state face (facet of 3 states), $n_i\le7$; continued $J_G,C_G$ vs Lemma L-two at real and complex $z$; $\omega_\beta=2+\frac94\sqrt2$ | `out_check_exact.txt` |
| `py -I check_pair.py` (1 s) | Theorem 1: exact $R$, Laguerre $\mathcal L$, the two-sided bound, and $h\mathbf K$ at $x=hn_i$ and $h(n_i-1)$ | `out_check_pair.txt` |
| `py -I check_facet.py` (~10 min; `--quick` ~40 s) | Theorem 2(a),(b) for the 3-cycle ($N'\le800$) and the 4-state face ($N'\le180$); radius independence | `out_check_facet.txt` |
| `py -I check_wide.py` (~40 s) | Theorem 2(a) across the layer, $x$ up to $0.4T$ | `out_check_wide.txt` |

The exact law comes from my own transfer-matrix recursion on the face (`dp_face` in `dl_lib.py`),
checked against brute force. The kernels use $J_G(\beta,z)$, $C_G(\beta,z)$ continued to complex
$z$ by Newton's method on the critical equation of the tilt, followed along the ray from $0$. The
contour is evaluated by the trapezoid rule with 192 nodes. Results:

* **P1 (exact lemma)**: relative differences $\le4\times10^{-16}$ in all three geometries. Facet
  functions agree with Lemma L-two to $7\times10^{-16}$. Holds.
* **P3, Theorem 1**: all 46 rows lie inside the explicit bound. Fixed $T=20$: $R/\mathcal L-1=
  1.8\times10^{-3}$, $1.8\times10^{-4}$ at $N'=10^4,10^5$ ($n_i=1$), and $7\times10^{-4}$ at
  $n_i=2000$, $N'=10^5$. Holds.
* **P4, lattice regime** $T=\sqrt{N'}$, $n_i=1,\dots,6$: $R/\mathcal L-1=0.09,\,0.03,\,0.010,\,0.003$ at
  $N'=10^2,\dots,10^5$ ($n_i=1$), while $R/(h\mathbf K(hn_i,S))-1\to-0.58$, $-0.59$. Holds.
* **P5 ($k\ge3$)**: the bound holds. 3-cycle, $n_i=1$: $E=0.0485,\,0.0244,\,0.0129,\,0.0072$ at
  $T=4$, $N'=100,\dots,800$, and $E=0.030$ at $T=16$, $N'=800$. Across the layer (`check_wide`,
  $T=8$): $E$ halves from $N'=200$ to $400$ at every fixed $x$, up to $x=1.6$. *The second half of
  P5 failed*: $E$ does not settle at a limit of order $1/T$. It tends to about $0$ at fixed $T$. That
  led to (3.1), which reduces the $1/T$ term to $O(T^{-2}+x^{1/2}T^{-3/2})$. For small $x$ the
  data look like $E\approx1.5h$ (3-cycle, $n_i=1$, $N'=800$: $E/h=1.45,\,1.39,\,1.50$ at
  $T=4,8,16$), far below $T^2/N$. $E$ grows with $x$, and at $x\asymp T$ it is of order $T^2/N$
  ($EN/T^2=1.3$ at $x=1.6$, $N'=400$). So the discretization of the facet runs does not cancel
  completely in the ratio. The 4-state face gives $E=0.021,\,0.014,\,0.011$ at $T=3$,
  $N'=60,120,180$, $n_i=1$.
* **P6 (lattice vs continuum kernel)**: $\mathcal L/(h\mathbf K(hn_i,S))-1=-0.041$, $-0.166$, $-0.50$ for
  $T=4,8,16$ at $N'=800$, $n_i=1$, close to $-\omega_\beta T^2/(2N)$ (predicted $-0.05,-0.21,-0.83$ to
  first order). It halves with $N'$ at fixed $T$. With $x=h(n_i-1)$ the difference is exactly $0$ at
  $n_i=1$, and at most $4\times10^{-2}$ in modulus for $T\le8$, $N'=800$, $n_i\le12$. Holds, with a practical caveat: the constant
  $\omega_\beta/2$ is large, so at moderate $N$ the lattice kernel is noticeably more accurate
  (e.g. $E=0.028$ against $-0.28$ at $N'=400$, $T=8$, $n_i=1$).
* **P7**: the contour value changes by $\le2\times10^{-15}$ between radii. Holds.
* **P2**: the normalization $P_N/P_{N'}\approx h\mathbf K$ is visible in the last two columns of
  `out_check_facet.txt`. Holds.

## 6. Honest status

* **Proved** (up to the usual referee check of my writing): Theorem 1 in full, explicit constants;
  Theorem 2(a),(b),(c) in the range $T_0\le T\le N^{1/2}$ (for (b),(c): $T\le\varepsilon_1N^{1/2}$).
  The proofs use only results proved in the paper plus the lemmas above. The steps I would
  double-check first are the bound $\bar b(\sigma\theta')\le\sigma b_r(\theta')$ in Lemma B, Step 2
  (it needs $X_{A(r)}(\theta'(\beta,r))\ge0$, which holds by Lemma critical(a)), and the saddle
  bookkeeping of Lemma C (constants $0.4$, $3$, $\frac1{10}$ are not optimized but are safe for
  $Z_0,T_0$ large and $\delta$ small).
* **Not proved**: (i) For $k\ge3$ in the lattice regime $T\asymp\sqrt N$, Theorem 2(a) still holds
  formally, but its error $T^2/N$ is of order one. A statement there needs the fully discrete
  local law on $G$, which is the content of item (O2). (ii) The numerically visible cancellation
  (error $\approx h(1+\omega Sx)$ instead of $T^2/N$) is not proved. (iii) For bounded $T$ the
  theorem is stated only for $T\ge T_0$ when $k\ge3$, like Theorem layer.
* **What to tell the referee (C1-F1)**: the boundary layer is now a theorem about the counts.
  The law of $n_i$ given $\hat n$ is $h$ times the continuum kernel at $x=hn_i$, $S=hN'$, up to
  $O(1/T+T^2/N)$, down to $n_i=1$. Bessel forms transfer verbatim. For pair faces, an exact
  discrete Pedler formula and an explicit Laguerre kernel hold at every $T$, including
  $T\asymp\sqrt N$, where the Bessel kernel fails.
* **Correction to the plan**: the claim that the lattice kernel "differs from the Bessel kernel
  when $n_i=O(1)$" is true only when $T^2/N\not\to0$. In the main range they differ by
  $O(T^2/N)$. Length estimate: Theorem 1 about 1.5 pages, Theorem 2 with Lemmas B, C about
  4 pages.
