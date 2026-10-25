# Audit of the discrete boundary layer (C1, item O1)

2026-10-25. Audits `01_report.md` in this folder against `kagey-problems/problem131/paperC`
(sec_boundary, sec_secondorder Lemma discrete, app_torus, app_laplace, sec_vertex). I read the
paper and changed nothing in it. Only the mathematics is judged here.

## 1. Claim cards

| # | Claim | Hypotheses and range |
|---|---|---|
| 1a | $P_N(n)/P_{N'}(\hat n)=R$, exact double binomial sum; $P_{N'}(\hat n)=\mu_jp_j^{N'-1}$ | $F=\{j,i\}$, $q_{ji},q_{ij},\mu_j>0$, $hq_{\max}\le1$ (stated $\le\frac12$), $N',n_i\ge1$ |
| 1b | $\mathcal L=p_i^{n_i}[B_{n_i}+c_1\frac h{p_i}B'_{n_i}+c_2\frac{h^2}{p_i^2}B''_{n_i}](u)$ | same |
| 1c | $1-\frac{U+2\sqrt U+2}{2N'}\le R/\mathcal L\le e^{2hq_j(1+2\sqrt U)}$; hence $R=\mathcal L(1+O(T/N+(T^2/N)\sqrt{n_i/N}))$ | bound: $hq_{\max}\le\frac12$; corollary: also $n_i\le N'$, $1\le T\le N^{1/2}$ |
| 1d | $\mathcal L=h\mathbf K(hn_i,S)(1+O(hS+h))$; for bounded $n_i$, $hS\asymp1$ the leading terms differ by a factor in $[1-\frac u2,1-\frac u2e^{-n_iu/2}]$ | $1\le n_i\le N'$, $hS\le1$ |
| 2a | $P_N(n)=P_{N'}(\hat n)\mathcal L_\beta(n_i,N')(1+E)$, $\lvert E\rvert\le C(T^{-2}+x^{1/2}T^{-3/2}+T^2/N)$ | $F$ irreducible, $k\ge2$, $G$ with (H), $\beta=\hat n/N'\in\mathcal K$, $1\le n_i\le\delta N$, $T_0\le T\le N^{1/2}$ |
| 2b | $\mathcal L_\beta=h\mathbf K_\beta(x',S)(1+O(T^2/N))$, $x'\in\{hn_i,h(n_i-1)\}$ | as 2a and $T\le\varepsilon_1N^{1/2}$ |
| 2c | Bessel forms of Theorem layer(b),(c) for the counts, with the extra $T^2/N$ | as 2b |
| N | the ratio of lattice laws carries exactly one power of $h$ | every $k\ge2$ |
| S | Theorem layer(a) holds with $\lvert E\rvert\le C(T^{-2}+x^{1/2}T^{-3/2})$ | as in Theorem layer |
| K | for $T\le\varepsilon N^{1/2}$ the lattice kernel is $hK_\beta(hn_i,S)(1+O(T^2/N))$, down to $n_i=1$ | = 2b |

## 2. Derivations done before reading the proofs

*Pair face.* Delete the $i$-blocks from a path with composition $(N',n_i)$. What remains is
$j^{N'}$. Each of the $N'-1$ gaps carries either $p_j$ (no block) or
$hq_{ji}(1-hq_i)^{\ell-1}hq_{ij}$; the start carries $\mu_j$ or $\mu_i(1-hq_i)^{\ell-1}hq_{ij}$;
the end carries $1$ or $hq_{ji}(1-hq_i)^{\ell-1}$. Marking blocks by $z$ and summing block
lengths over compositions of $n_i$ into $K$ parts gives
$P_N(n)=\sum_K\binom{n_i-1}{K-1}p_i^{n_i-K}[z^K](\mu_j+zh\mu_iq_{ij})(1+zhq_{ji})(p_j+zh^2\omega)^{N'-1}$.
Dividing by $\mu_jp_j^{N'-1}$ and expanding gives exactly the report's $R$, with
$c_2=\frac{\mu_i}{\mu_j}\omega$. Agrees with 1a.

*Why half-discretization keeps positivity.* In Lemma runs write each term as
$u_m=\kappa_mv_m$ where $v_m$ replaces only the facet binomials
$h^{m_j-1}\binom{n_j-1}{m_j-1}(1-hq_j)^{n_j-m_j}$ by $e^{-q_js_j}s_j^{m_j-1}/(m_j-1)!$ and keeps
$h^{m_i}\binom{n_i-1}{m_i-1}p_i^{n_i-m_i}$. Every factor of $v_m$ is $\ge0$ (it is $W(m)\ge0$
times positive numbers), and $\kappa_m$ is the same product as in (A-kappa) restricted to $G$.
So $P_N(n)/\sum v_m=\mathbb E_w\kappa_m$ for a genuine probability $w$, and Steps 2 to 4 of the
proof of Lemma discrete apply with $M_G$ in place of $M$. The only new input is a bound
$\log\mathbb E_we^{M_G-1}\le CT$, and the rates-out-of-$G$ scaling by $\sigma=e$ gives it, since
every $G$-letter except possibly the last is followed by a jump out of it. Grouping $v_m$ by
$m_i=K$ and using the regrouping in the proof of Lemma layer-exact gives
$\sum v_m=h^{k-1}\sum_Kb_K[z^K]f^{(z)}_G(s)=h^{k-1}\mathbf D$. This matches Lemma B.

## 3. Line-by-line check

**Theorem 1.** (a), (b): correct. (c): $\rho_m=\prod_{l\le m}(1-l/N')\,p_j^{-m}$ is right; the
ratio test $\beta_{K+1}/\beta_K\le U/(K(K+1-e))$ gives $\mathbb E[(m+e-1)m]\le U$ for each $e$
(the boundary terms vanish); $\mathbb E m\le1+\sqrt U$ and
$\mathbb E m(m+1)\le U+2\sqrt U+2$ follow; the log-derivative bound
$\log\mathbb Ee^{cm}\le c(1+\sqrt{\sigma U})$ is right, and $\sqrt e<2$. The corollary uses
$1/N'\le2h$, which needs $T\ge1$ and $n_i\le N'$, both stated. Correct as written. The implied
constant is large near $T\asymp N^{1/2}$ (for example $R/\mathcal L-1=1.39$ at $N'=10^3$,
$T=\sqrt{N'}$, $n_i=200$), but the upper bound $e^{2hq_j(1+2\sqrt U)}$ stays bounded there, so
the $O$ statement holds.

(d), first claim: **the written proof has two slips**. (i) $\mathcal L/(h\mathbf K)$ equals the
average of the term ratio against the law proportional to the terms of $\mathbf K$, not against
$\nu$ of (c), which is proportional to the terms of $\mathcal L$. With $\nu$ one controls
$h\mathbf K/\mathcal L=\mathbb E_\nu[1/\text{ratio}]$, and $1/(1-K(K-1)/2n)$ is not controlled by
moments. (ii) The $e=2$ weight is compared with the $e=0$ weight only, which gives $O(h/S)$; that
is not $O(h)$ when $S<1$, and no lower bound on $S$ is assumed. Both are repaired in a few lines:
for the law $\nu'$ proportional to the terms of $\mathbf K$ the ratio test reads
$\le\omega Sx/(K(K+1-e))$, so the same moment bounds hold with $U'=\omega Sx\le U$; and
$\nu'(e=2)\le c_2x/(c_1+S\omega)$, so the constant $2$ contributes $O(x/n)=O(h)$. Numerically the
claim holds at small $S$: $(\mathcal L/h\mathbf K-1)/h\to1.73$ as $T\to0$ for $N'\in\{1,2,5\}$,
$n_i\le N'$. Second claim (the factor $[1-\frac u2,1-\frac u2e^{-n_iu/2}]$): correct, using
$\mathcal I(y)\le e^{y/2}$ (from $(j+1)!\ge2^j$) and the series in the proof of Lemma
uniform-laguerre-bessel.

**Lemma D.** A coefficient-of-$x^{K-1}$ restatement of the regrouping in the proof of Lemma
layer-exact, valid for any nonnegative rates, with $q_G$ in the exponent arbitrary. Correct.

**Schwarz step (3.1).** $\varepsilon=f^{(z)}_G/\Lambda-1$ is holomorphic on $\lvert z\rvert<2z_0$
because $C_G(\beta,z)\ne0$ there (Step 1(i),(ii) of the proof of Theorem L-facet:
$\lvert\chi\rvert\ge c_\chi$, $\operatorname{Re}\mathcal J\ge\frac12\sigma_0$), and
$\lvert\varepsilon\rvert\le C/S$ on $\lvert z\rvert\le z_0$ for $S\ge1$. Schwarz applied to
$(\varepsilon-\varepsilon(0))S/(2C)$ gives (3.1), uniformly. Correct. The same step proves the
sharpening S of Theorem layer(a): divide by $f_G=\Lambda(0)(1+\varepsilon(0))$, and only
$\varepsilon(z)-\varepsilon(0)$ enters, against $\mathcal A^{\rm abs}\le C\mathcal A$ on a circle of
radius $\rho\le C/S$ (few visits) or $\rho\le2z_*$ (many visits). **Proved.**

**Lemma C (the $z$-contour).** Checked each inequality. Few visits: $\lvert w_d\rvert\le
e^{\tilde x/\rho}\le e^{\tilde\zeta/2}$, $b_1=p^{n-1}\ge e^{-2q_i\tilde x}$ with $\tilde x$
bounded, $\lvert\Xi-1\rvert\le C/S$; fine. Many visits: $a=2h\omega S/\tilde\zeta\le2\omega_{\max}/Z_0$
uses only $hS\le1$; the sign change of $\lambda_d'$ at $\tilde z_*/2$ and $2\tilde z_*$ is right
($-4\omega S/(1+2a)$ and $\ge-\omega S/2$); $(2p+y)/(p+y)^2\ge1.44\ge4/9$ for $p\in[\frac12,1]$,
$y\le\frac14$, so $\lambda_d''>0$ on $I$; the gap uses $\lvert p+a'e^{-\mathrm i\phi}\rvert$ largest
at $\phi=0$ plus the paper's $R$ estimate; $(n-1)a'/p=\tilde x/(p\rho)=S\omega\rho(1+\eta)(1+a'/p)\le3\zeta_d$
bounds the log-term derivatives; $-\ell''(0)=(1+\eta)\frac{2p\rho+h}{p\rho+h}+O(\rho+1/S)\in[0.4,3]$;
$\ell(-\phi)=\overline{\ell(\phi)}$ makes $\ell(0)$, $\ell''(0)$ real, so Remark laplace-uniform
applies with $m=1$, $T\to\zeta_d\ge Z_0/4$. (3.3) follows. Correct. The uniformity in $n_i$ down
to $1$ is clean ($n_i=1$: $w_d\equiv1$, few visits, $\rho=1/S$) and up to $\delta N$ only uses
$x\le\delta T$, $S\ge(1-\delta)T$, $z_*\le\sqrt{2\delta/\omega_{\min}}$.

**Lemma B.** Step 1 as in Section 2 above. Step 2: $A'(z)=\sigma A(z)$, $\mu'=\mu$,
$e'=\ones+z\sigma c^-\le\sigma e^{(z)}$, $d'=q_G-z\sigma c^-\circ c^+$, all coefficients
nonnegative, so $[z^K]f'\le\rho^{-K}f'^{(\rho)}$. In the Claim, the scaling
$X_{\sigma A}(\sigma z')=\sigma^{-1}X_A(z')$ leaves the first factor of $\bar b$ unchanged and
bounds the second by $\sigma$ times that of $b_r$, because $X_{A(r)}(\theta'(\beta,r))\ge0$;
admissibility follows from Lemma critical(a),(c); $\Lambda(r)$ for real $r$ is identified by
Lemma critical(e). Then $\mathbf D'/\mathbf D\le C\zeta_d^{1/2}S^{(k-2)/2}e^{CS}\le e^{C'T}$ using
(3.2) and $\mathbf D\ge\frac12\mathcal A_d$. Step 3 is Step 4 of Lemma discrete verbatim, with
$n^G_{\min}\ge\varepsilon_{\mathcal K}N/2$ from $n_i\le\delta N\le N/2$. Correct.

**Theorem 2(a).** $P_{N'}(\hat n)=h^{k-2}f_G(s)(1+O(T^2/N))$ is Lemma discrete for the face $G$
with $N'$ steps and the same $h$; it needs $1\le S\le N'^{1/2}$, which follows from
$h^2N'\le T^2/N\le1$, and its error $S^2/N'\le T^2/N$. For $|G|=1$, (vertexmax) with $S\ge1$.
The factor $1+\varepsilon(0)$ cancels, leaving $O(\rho/S+T^2/N)$. **Proved as written.**

*Range of $T$.* Nothing in the proof uses Theorem A or the stratified law (the source of
$T\le N^{1/3}$). The inputs are Theorem L-facet (continuum, all $S\ge1$), Lemma discrete on $G$
and the comparison of Lemma B (both $T\le N^{1/2}$), and Lemma C (only $hS\le1$). So
$T\le N^{1/2}$ is the right range. One caveat for the write-up: at $T\asymp N^{1/2}$ the bound
$\lvert E\rvert\le C$ may exceed $1$, so there the statement is only an upper bound up to a
constant; the two-sided content needs $T\le\varepsilon N^{1/2}$. Section 6 of the report says
this in words, and the theorem should say it too.

**Theorem 2(b).** On the circle of the proof of Theorem layer(a) for $x'$:
$h/\rho\le\max(hS,4h\omega S/Z_0)$, $\tilde x/\rho^2\le4\omega S$, so
$(n-1)\lvert y\rvert^2\le C(hS+hx)\le CT^2/N$ and $w_d=e^{x'/z-q_ix'}(1+O(T^2/N))$; with
$\mathcal A^{\rm abs}\le C\mathcal A$ this gives (b). $\mathbf K_\beta(0,S)=[z]\widetilde\Lambda_\beta$
is the $x\to0$ limit of $\mathbf K_\beta$. **Proved.** Claim K is this statement.

**Theorem 2(c).** The proofs of Theorem layer(b),(c) are statements about
$\mathbf K_\beta/\mathbf B_\beta$ alone (the displays "$\mathbf K_\beta=\mathbf B_\beta(1+O(1/T+\sqrt{x/T}))$
for $x\le1$", "$\mathbf K_\beta=\mathbf B_\beta\exp(O(\sqrt{x/T}(1+x)))$", and
$1+c_1z_*I_0/I_1+O(x/T)$ in the case $\pi^{\rm in}_\beta=\pi^{\rm out}_\beta$), so they combine with
(a),(b). Passing between $1+O(\cdot)$ and $e^{O(\cdot)}$ needs $T^2/N$ small, which (b) assumes.
The cross term $c_1z_*\frac{I_0}{I_1}\cdot O(1/T+T^2/N)$ is absorbed since $c_1z_*I_0/I_1$ is
bounded. **Proved.**

**Normalization N.** $P_N\approx h^{k-1}f_F$, $P_{N'}\approx h^{k-2}f_G$ (Lemma continuum with
$N^{-(k-1)}f_T=h^{k-1}e^{-\langle q,t\rangle}H$), ratio $h\mathbf K$. Confirmed by 2b and by the
numerics. **Proved.**

## 4. Independent computations

My own code, outside the repository, run with `py -I`.

* **Theorem 1(a) against brute force**, exact rational arithmetic: a pair face inside a
  3-state chain with killing (rates $q_{ji}=\frac32$, $q_{ij}=2$, killing $\frac12,\frac13$,
  $\mu=(\frac25,\frac15,\frac25)$), every $N\le12$, $h\in\{\frac17,\frac1{13}\}$, every
  $1\le n_i<N$: $P_N(n)=R\cdot\mu_jp_j^{N'-1}$ **exactly**, and $P_{N'}(\hat n)=\mu_jp_j^{N'-1}$
  exactly.
* **Theorem 1(c)**: 83 rows, $N'\in\{10,\dots,10^4\}$, $T\in\{\frac12,1,3,10,\sqrt{N'}\}$,
  $n_i\le N'$ up to $2000$: zero violations of the two-sided bound. At $n_i=1$, $T=\sqrt{N'}$:
  $R/\mathcal L-1=6.5\cdot10^{-2}$, $2.0\cdot10^{-2}$ at $N'=10^3,10^4$ (scales like
  $N^{-1/2}$), while $\mathcal L/(h\mathbf K)-1=-0.70$, $-0.71$.
* **Theorem 2, $k=3$.** Exact law by my own transfer-matrix recursion (checked against brute
  force on 3 states with killing, $N\le9$, all compositions, max relative difference
  $6\cdot10^{-15}$); kernel from the closed forms of Lemma L-two, Taylor coefficients of
  $\widetilde\Lambda_\beta$ by a 400-node contour at 50 digits. Here $h=T/N$ with $N=N'+n_i$.

  3-cycle of Prop. layer-cubic(e), uniform start, $i=3$, $\beta=(\frac12,\frac12)$:

  | $N'$ | $T$ | $n_i$ | $T^2/N$ | $E$ | $EN/T^2$ | $\mathcal L/h\mathbf K(h(n_i-1))-1$ |
  |---|---|---|---|---|---|---|
  | 200 | 8 | 10 | 0.305 | 0.187 | 0.61 | $-0.141$ |
  | 400 | 8 | 10 | 0.156 | 0.072 | 0.46 | $-0.079$ |
  | 800 | 8 | 10 | 0.079 | 0.029 | 0.36 | $-0.035$ |
  | 1600 | 8 | 10 | 0.040 | 0.012 | 0.30 | $-0.013$ |
  | 1600 | 4 | 1 | 0.010 | $4.5\cdot10^{-3}$ | 0.45 | 0 |
  | 1600 | 40 | 20 | 0.988 | 0.357 | 0.36 | $-0.737$ |

  Second geometry, $i=2$ (middle state), $\beta=(0.3,0.7)$, $\mu=(0.5,0.2,0.3)$: same picture,
  $EN/T^2\in[0.17,0.82]$ over $N'\le1600$, $T\in\{4,8\}$, $n_i\in\{1,5,30\}$. In all 68 rows (both
  geometries, plus $T\in\{\frac12\sqrt{N'},\sqrt{N'}\}$ at $N'=400,1600$) $0<E\le0.91\,T^2/N$. At fixed $T=4$, $n_i=1$, a fit
  $E\approx E_\infty+ch$ gives $c\approx1.08$ from both $N'$ pairs and $E_\infty\approx1.8\cdot10^{-3}$;
  at $T=8$, $E_\infty\approx4\cdot10^{-4}$. The ratio $\approx4.9$ is close to the $T^{-2}$ that
  the Schwarz sharpening predicts as $x\to0$. Theorem 2(b) is visible in the last column, which
  shrinks like $1/N$.
* My values differ slightly from `out_check_facet.txt` because that script uses
  $\mu=(0.4,0.35,0.25)$. It also sets $h=T/N'$. So its column "T" is $S=hN'$, and "T^2/N" is
  $S^2/N$. This is a labelling point in the numerics, not in the mathematics, but the values
  quoted as "$T=4,8,16$" in P5 and P6 of the report are values of $S$.

## 5. Verdicts

| Result | Verdict |
|---|---|
| Theorem 1(a), (b) | proved as written |
| Theorem 1(c) | proved as written |
| Theorem 1(d), first claim | statement correct, proof incomplete: average against the law of the $\mathbf K$-terms, not $\nu$, and compare the $e=2$ weight with $c_1+S\omega$, not $S\omega$ (fix in Section 3) |
| Theorem 1(d), second claim | proved as written |
| Theorem 2(a) | proved as written; state that it is two-sided only for $T\le\varepsilon N^{1/2}$ |
| Theorem 2(b), (c) | proved as written |
| One power of $h$ | proved |
| Schwarz sharpening of Theorem layer(a) | proved |
| Correction: lattice kernel $=h\mathbf K_\beta(hn_i,S)(1+O(T^2/N))$ for $T\le\varepsilon N^{1/2}$ | proved (it is Theorem 2(b)) |

No refutation was found. The numerics confirm the order $T^2/N$ for $k=3$ with a small constant
($\le0.91$). The lattice-kernel versus continuum-kernel gap has the same order with a larger
constant, so for $k\ge3$ the lattice kernel is the more accurate approximation at moderate $N$.
