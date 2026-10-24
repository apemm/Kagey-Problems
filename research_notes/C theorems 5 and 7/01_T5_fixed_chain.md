# Theorem 5(a). Finite-horizon recovery for a fixed chain and a fixed start

Route T5-A of `00_targets.md`, Target 1 part (5a). Date October 24, 2026.
Base checkpoint `6add913`.

Inputs read in full, at the base checkpoint.

- `research_notes/C theorems 5 and 7/00_targets.md`.
- `kagey-problems/problem131/paperC/sec_model.tex` (setting, `lem:admissible`, `lem:runs`,
  `eq:vertexmax`, `lem:continuum`).
- `kagey-problems/problem131/paperC/sec_secondorder.tex` (`def:tilt`, `prop:constant`,
  `thm:local`, `lem:discrete`, `thm:facemax`, `thm:crossing`, `thm:window`, `prop:nextterm`,
  `prop:weakfield`).
- `kagey-problems/problem131/paperC/sec_firstorder.tex`, lines 180 to 490 (`prop:rate`,
  `lem:upper`, `thm:first`).
- `kagey-problems/problem131/paperC/app_torus.tex` (`lem:perron`, proof of `prop:constant`(a),
  `lem:torus`, proof of `lem:upper`, proofs of `thm:local` and `lem:discrete`, proof of
  `thm:first`(ii), `lem:forest`).
- `kagey-problems/problem131/paperC/app_laplace.tex` (`lem:laplace`, `lem:laplace2`).
- `research_notes/Occupation novelty and compact advances/11_C_ready_to_draft_outline.md`,
  Sections 1, 2, 3 and 5.
- `research_notes/Occupation novelty and compact advances/12_Good_original_closure.md`,
  Section 2 (in particular 2B, the whole-face bound with a Perron tilt).
- `research_notes/Local probability novelty and uniqueness/04_C_uniqueness_proof.md` (the
  convexity and secant argument for crossings, which is the "log-convexity and secant bounds"
  route that the target names).
- `research_notes/C and F final outline audit/02_C_proof_audit.md`, lines 130 to 170.

The script `01_pair_entry_check.py` in this folder does the numerical check. It runs with
`py -I 01_pair_entry_check.py`, and its printed output is reproduced in Section 9.

## 0. Notation

We use the notation of the paper. So $A_F=(q_{ij})_{i,j\in F}$ is the off-diagonal part with
zero diagonal, and $Q_F=A_F-\operatorname{diag}(q_i)_{i\in F}$ keeps the original exit rates.
The matrix that `00_targets.md` calls $A_F-\operatorname{diag}v$ is our
$-Q_F-\operatorname{diag}v_F=\operatorname{diag}(q-v)_F-A_F$. Its smallest real eigenvalue is
$$\lambda_F(v)=-\varrho\bigl(Q_F+\operatorname{diag}v_F\bigr)=-\varrho\bigl(A_F-\operatorname{diag}(q-v)_F\bigr).$$
So the field replaces the killed diagonal $q_i$ by $q_i-v_i$. In the reversible case
$\lambda_F(v)=\lambda_{\min}(S_F-\operatorname{diag}v_F)$, since $S_F-\operatorname{diag}v_F$ is
the symmetrization of $-(Q_F+\operatorname{diag}v_F)$ by $D_{\sqrt\pi}$.

We write $L=\log N$, $T=\tau L$, $h=T/N$, $\alpha=n/N$, and
$$w_{\tau,v}(n)=P_N(n)\,e^{T\langle v,n\rangle/N},\qquad
M_F(T,v)=\max\{w_{\tau,v}(n):\operatorname{supp}n=F\},$$
with $\max\emptyset=0$. The leading score is $\Phi_{\tau,v}(F)=|F|-1+\tau\lambda_F(v)$. A face $G$
is the *unique maximizing support* at $(\tau,v)$ if $M_G(T,v)>M_F(T,v)$ for every face $F\ne G$.
We write $q_{\max}=\max_iq_i$.

## 1. Statement

**Hypotheses.**

- (A1) $Q$ is an irreducible reversible generator on $[d]$, $d\ge2$, with stationary law $\pi$.
  Its support graph $G=([d],E)$ is connected, known and labelled, with $m=|E|$ edges.
- (A2) $\lVert S\rVert_2\le R$ for $S=D_{\sqrt\pi}(-Q)D_{\sqrt\pi}^{-1}$, and
  $\sqrt{w_{ij}}\ge b>0$ for every edge $\{i,j\}\in E$, where $w_{ij}=q_{ij}q_{ji}$.
- (A3) The start $\mu$ is fixed and has full support.

**Design (C-I1).** Put $H=2R$, $\tau_0=1/(2R)$, $U=8R/b^2$ and $M=4R+4UR^2$. For an ordered
pair $(i,j)$ of distinct states and $\delta\in\mathbb R$ let $v=v^{(i,j,\delta)}$ be the field
with $v_i=\delta$, $v_j=0$ and $v_k=-M$ for $k\notin\{i,j\}$. The protected rectangle is
$|\delta|\le3R$, $1/(4R)\le\tau\le U$.

**Coordinates.** The limiting coordinates are $x_i=q_i-q_1$ for $i\ne1$, and for an edge
$\{i,j\}$ (with an orientation fixed by the design)
$$t_{ij}=\frac{\sqrt{(H-\Delta_{ij})^2+4w_{ij}}+H-\Delta_{ij}}{2w_{ij}},\qquad
\Delta_{ij}=x_i-x_j=q_i-q_j .$$
The finite-horizon coordinates are $x_{i,N}$, the value of $\delta$ at which the exact maximizing
support at $(\tau_0,v^{(i,1,\delta)})$ changes from $\{1\}$ to $\{i\}$, and $t_{ij,N}$, the
smallest $\tau\in[1/(4R),U]$ at which $\{i,j\}$ is an exact maximizing support at
$(\tau,v^{(i,j,H)})$. Parts (a) and (b) of the theorem show that both are well defined for large
$N$. Finally $\Psi$ is the reconstruction map of C-I1, recalled in Section 7, which sends
coordinates $(d,t)$ to a generator.

**Theorem 5(a).** Assume (A1) to (A3). There is $N_0$, depending on $Q$, $\mu$, $R$ and $b$,
such that the following holds for every $N\ge N_0$.

(a) *Singleton switches.* Let $i\ne1$ and $\tau=\tau_0$. For every $\delta\in[-3R,3R]$ other
than one point $x_{i,N}$, the maximizing support at $(\tau_0,v^{(i,1,\delta)})$ is unique. It is
$\{1\}$ for $\delta<x_{i,N}$ and $\{i\}$ for $\delta>x_{i,N}$. Exactly
$$x_{i,N}=\frac{1}{\tau_0L}\Bigl[\log\frac{\mu_1}{\mu_i}+(N-1)\log\frac{1-hq_1}{1-hq_i}\Bigr],
\qquad h=\frac{\tau_0L}N,$$
and hence
$$x_{i,N}=x_i+\frac{2R\log(\mu_1/\mu_i)}{\log N}+O\Bigl(\frac{\log N}N\Bigr).$$

(b) *Pair entry.* Let $\{i,j\}\in E$ and $\delta=H$. For every $\tau\in[1/(4R),U]$ other than one
point $t_{ij,N}$, the maximizing support at $(\tau,v^{(i,j,H)})$ is unique. It is $\{i\}$ for
$\tau<t_{ij,N}$ and $\{i,j\}$ for $\tau>t_{ij,N}$. Moreover
$$t_{ij,N}=t_{ij}\Bigl(1-\frac{\log\log N}{2\log N}\Bigr)+\frac{c_{ij}}{\log N}
+O\Bigl(\frac{\log\log N}{(\log N)^2}\Bigr),\qquad
c_{ij}=-\frac{t_{ij}}2\Bigl(\log t_{ij}+2\log\frac{K_{ij}(v)}{\mu_i}\Bigr),$$
where $K_{ij}(v)>0$ is the constant of Lemma 1 for the face $\{i,j\}$ and the field
$v=v^{(i,j,H)}$. In particular
$t_{ij,N}=t_{ij}\bigl(1-\frac{\log\log N}{2\log N}\bigr)+O(1/\log N)$.

(c) *Reconstruction.* Let $d_N=(0,x_{2,N},\dots,x_{d,N})$, let $t_N=(t_{ij,N})_{\{i,j\}\in E}$, and
put $\varepsilon_N=\log\log N/(2\log N)$. Then $Q_N=\Psi(d_N,t_N)$ and
$\widetilde Q_N=\Psi(d_N,t_N/(1-\varepsilon_N))$ are irreducible reversible generators on $G$, and
$$\lVert Q_N-Q\rVert_2=O\Bigl(\frac{\log\log N}{\log N}\Bigr),\qquad
\lVert\widetilde Q_N-Q\rVert_2=O\Bigl(\frac1{\log N}\Bigr).$$
The first rate is attained, that is $\lVert Q_N-Q\rVert_2\ge c\log\log N/\log N$ for some $c>0$.

(d) *Suppression.* For every ordered pair $(i,j)$, uniformly on the protected rectangle, every
face $F\notin\{\{i\},\{j\},\{i,j\}\}$ has
$M_F\le C(\log N)^{d-1}N^{-3/4}\max(M_{\{i\}},M_{\{j\}},M_{\{i,j\}})$.

All implied constants depend on $Q$, $\mu$, $R$ and $b$ only. The proof occupies Sections 2 to 7.
The order is Lemma 1 (controlled face maximum), Lemma 2 (singleton atom), Lemma 3
(suppression), Lemma 4 (convexity and slope), then the crossings, then Lemma 5
(reconstruction).

## 2. Lemma 1. The controlled face maximum

### 2.1 Three identities

Let $F$ be a face with $k=|F|\ge2$. For $p\in\mathbb R^F$ put
$$I^p_F(\alpha)=\sup_{u\in(0,\infty)^F}\sum_{i\in F}\alpha_i\Bigl(p_i-\frac{(A_Fu)_i}{u_i}\Bigr),
\qquad\lambda^p_F=-\varrho(A_F-\operatorname{diag}p).$$
So $I^q_F=I_F$ and $\lambda^q_F=\lambda_F$, and $\lambda^{q-v}_F=\lambda_F(v)$. Three identities
carry the field through the existing proofs.

(I1) For $\operatorname{supp}n=F$ and $\alpha=n/N$ we have $e^{T\langle v,n\rangle/N}=e^{T\langle v,\alpha\rangle}$.

(I2) By `lem:continuum`, $f_T(\alpha)e^{T\langle v,\alpha\rangle}=T^{k-1}e^{-T\langle q-v,\alpha\rangle}H(T\alpha)$,
and $H$ depends only on $A_F$ and $\mu$.

(I3) $I_F(\alpha)-\langle v,\alpha\rangle=I^{q-v}_F(\alpha)$, since $p$ enters $I^p_F$ only
through the linear term $\langle p,\alpha\rangle$.

Note that every object of `def:tilt` is free of $q$. The vector $r_\alpha$ maximizes
$u\mapsto\langle q-A_Fu/u,\alpha\rangle$, that is, it minimizes $u\mapsto\langle A_Fu/u,\alpha\rangle$.
Hence $r_\alpha$, $l_\alpha=\alpha/r_\alpha$, $\theta(\alpha)=A_Fr_\alpha/r_\alpha$,
$\widehat Q_\alpha$, $\Sigma_\alpha$ and $C_F(\alpha)$ depend on $A_F$, $\mu$ and $\alpha$ only.
The exit rates enter the local law only through the explicit factor $e^{-T\langle q,\alpha\rangle}$,
and (I2) absorbs the field into that factor.

### 2.2 Which steps of the existing proofs change

We go through the inputs of `thm:facemax` with $q$ replaced by $p=q-v$ where the continuum is
concerned. Note that $p_i=q_i-v_i$ can be negative. In the design $v_i=H=2R\ge2q_i$, so
$q_i-v_i\le-R<0$. So we must check that no step uses $p\ge0$, or that $p_i$ dominates the
$i$-th row sum of $A_F$.

1. *The rate* (`prop:rate`). Parts (a), (b) and (d) hold for $I^p_F$ and $\lambda^p_F$ for every
   $p\in\mathbb R^F$. The proof writes the killed matrix as $B-cI$ with $B\ge0$ and some real
   $c$, and uses $p$ only in the linear term. No sign of $p$ is used. With $p=q-v$ we get
   $I_F-\langle v,\cdot\rangle\ge\lambda_F(v)$ on $\Delta_F$, with equality exactly at
   $\alpha^*_F(v)=l_F(v)\circ r_F(v)$, and every point of $\partial\Delta_F$ has a strictly larger
   value. Here $r_F(v)$ and $l_F(v)$ are the positive right and left Perron vectors of
   $Q_F+\operatorname{diag}v_F$ with $l_F(v)\cdot r_F(v)=1$.
2. *The Perron root lemma* (`lem:perron`). It is a statement about an irreducible generator $G$
   with stationary law $\pi$. In the proof of `thm:local` it is applied only at
   $G=\widehat Q_\alpha$, which is free of $q$. It does not change.
3. *The Hessian of the rate* (`prop:constant`(a)). Since $I^p_F-I_F$ is linear in $\alpha$, we
   have $\nabla^2I^p_F=\nabla^2I_F=\Sigma_\alpha^{-1}$ on $\Delta_F^\circ$ for every $p$. It does
   not change.
4. *The torus representation* (`lem:torus`). It involves only $A_F$ and $\mu$. It does not change.
5. *The Laplace lemma* (`lem:laplace`). In the proof of `thm:local` it is applied to the phase
   $\Psi(\alpha,\varphi)=\alpha_1g(z')+\sum_{i\ge2}\alpha_iz_i$ with $z_i=\theta_i(\alpha)e^{\mathrm i\varphi_i}$
   and the amplitude $\chi(\alpha,\varphi)=b(z')\prod_{i\ge2}z_i$. Both are free of $q$. It does
   not change. Hence `thm:local`, divided by $e^{-T\langle q,\alpha\rangle}$, reads
   $T^{k-1}e^{-T\langle\theta(\alpha),\alpha\rangle}H(T\alpha)=T^{(k-1)/2}C_F(\alpha)(1+O_{\mathcal K}(1/T))$,
   a statement without $q$. We multiply it by $e^{-T\langle q-v,\alpha\rangle}$ and use (I2) and
   $I_F(\alpha)=\langle q-\theta(\alpha),\alpha\rangle$. For every compact
   $\mathcal K\subset\Delta_F^\circ$, uniformly for $\alpha\in\mathcal K$, $T\ge1$ and *all*
   $v\in\mathbb R^d$,
   $$f_T(\alpha)e^{T\langle v,\alpha\rangle}=T^{(k-1)/2}C_F(\alpha)\,e^{-T(I_F(\alpha)-\langle v,\alpha\rangle)}\bigl(1+O_{\mathcal K}(1/T)\bigr).\tag{2.1}$$
   The implied constant is the one of `thm:local` and does not depend on $v$.
6. *Discrete and continuum* (`lem:discrete`). By (I1) and (I2) the ratio of $w_{\tau,v}(n)$ to
   $N^{-(k-1)}f_T(n/N)e^{T\langle v,n/N\rangle}$ is the ratio $P_N(n)/(N^{-(k-1)}f_T(n/N))$ of the
   lemma. It does not change. Note that the discrete chain keeps its rates $q$, and the condition
   $hq_{\max}\le\frac12$ refers to them.
7. *The whole-face upper bound* (`lem:upper`). It does not change as a statement. We only choose
   the tilt $\theta(v)=q-v-\lambda_F(v)\ones$. It lies in
   $V_F=\{\theta:\varrho(A_F-\operatorname{diag}\theta)=0\}$, because
   $A_F-\operatorname{diag}\theta(v)=Q_F+\operatorname{diag}v_F+\lambda_F(v)I$. Note that $V_F$
   itself is free of $q$.
8. *The face maximum* (`thm:facemax`). Three things change. The centre of the ball is
   $\alpha^*_F(v)$, the radius and the constants must be uniform in $v$, and the finite cover of
   tilts that excludes compositions near $\partial\Delta_F$ must be uniform in $v$. The step for
   bounded $T$ is not needed, since we take $T\ge T_1$.

### 2.3 The tilt and the constant are positive and analytic in the field

For every $v$ the matrix $Q_F+\operatorname{diag}v_F$ is an irreducible Metzler matrix (under
(H)), so its Perron root is a simple eigenvalue. By the implicit function theorem
$\lambda_F(v)$, $r_F(v)$ (normalized by $\sum_ir_{F,i}(v)=1$) and $l_F(v)$ (normalized by
$l_F(v)\cdot r_F(v)=1$) are real-analytic on $\mathbb R^F$, and both vectors are positive. Hence
$\alpha^*_F(v)\in\Delta_F^\circ$ is real-analytic in $v$.

At $\alpha=\alpha^*_F(v)$ the vector $u=r_F(v)$ attains the supremum in $I^{q-v}_F$ (item 1),
so $r_{\alpha^*_F(v)}$ is a multiple of $r_F(v)$ and
$$\theta\bigl(\alpha^*_F(v)\bigr)=q-v-\lambda_F(v)\ones,\qquad
\theta_i\bigl(\alpha^*_F(v)\bigr)=\sum_{j\in F\setminus\{i\}}q_{ij}\frac{r_{F,j}(v)}{r_{F,i}(v)}>0 .$$
The entries are positive because every row of $A_F$ has a positive entry when $F$ is irreducible
and $k\ge2$. This is the positive Perron tilt of `11_C_ready_to_draft_outline.md`, C-P3. Put
$$K_F(v)=C_F\bigl(\alpha^*_F(v)\bigr)=\frac{(\mu\cdot r_F(v))\,(l_F(v)\cdot\ones)}{(2\pi)^{(k-1)/2}\sqrt{\det\Sigma_{\alpha^*_F(v)}}}.$$
By `prop:constant`(a), $C_F$ is real-analytic and positive on $\Delta_F^\circ$ (positivity uses
$\mu(F)>0$). Hence $K_F$ is real-analytic and positive on $\mathbb R^F$. For a singleton we put
$K_{\{i\}}=\mu_i$. For a reversible pair $F=\{i,j\}$, `prop:constant`(b) with $\nu=\pi$ gives the
closed form
$$K_{ij}(v)=\frac{\bigl(\sum_{a\in F}\mu_a\phi_a/\sqrt{\pi_a}\bigr)\bigl(\sum_{a\in F}\phi_a\sqrt{\pi_a}\bigr)\,w_{ij}^{1/4}}{\sqrt{4\pi}\,(\phi_i\phi_j)^{3/2}},\tag{2.2}$$
where $\phi$ is the positive unit ground vector of the symmetric matrix $S_F-\operatorname{diag}v_F$
and $\pi$ in $\sqrt{4\pi}$ is the number. (Take $r=\phi/\sqrt{\pi_F}$ and $l=\phi\sqrt{\pi_F}$, so that
$l\circ r=\phi\circ\phi=\alpha^*$, and $c_{ij}(\alpha^*)=\phi_i\phi_j\sqrt{w_{ij}}$.)

Lemma `lem:perron`, applied at $G=R^{-1}(Q_F+\operatorname{diag}v_F+\lambda_F(v)I)R$ with
$R=\operatorname{diag}r_F(v)$, also gives $\nabla_v\lambda_F(v)=-\alpha^*_F(v)$. We do not need this.

### 2.4 Statement and proof

**Lemma 1 (controlled face maximum).** Let $F$ satisfy (H) with $k=|F|\ge2$, and let
$\mathcal V\subset\mathbb R^d$ be compact.

(a) There is $C$ such that for all $N\ge2$, all $T>0$ with $hq_{\max}\le\frac12$ and all
$v\in\mathcal V$,
$$M_F(T,v)\le C\,h^{k-1}e^{-T\lambda_F(v)+CT^2/N}.$$

(b) There are $T_1$, $N_0$ and $C$ such that for $N\ge N_0$, $T_1\le T\le N^{1/3}$ and
$v\in\mathcal V$,
$$M_F(T,v)=N^{-(k-1)}T^{(k-1)/2}K_F(v)e^{-T\lambda_F(v)}(1+E),\qquad|E|\le C\Bigl(\frac1T+\frac{T^2}N\Bigr),$$
and every maximizer $\hat n$ has $\hat n/N=\alpha^*_F(v)+O(1/T)$. In particular, for
$T=\tau L$ with $\tau$ in a compact interval of $(0,\infty)$, $E=O(1/L)$ uniformly in $\tau$ and
$v\in\mathcal V$.

*Proof.* (a) Let $\supp n=F$. By `lem:upper` with $\theta=\theta(v)=q-v-\lambda_F(v)\ones\in V_F$,
$$w_{\tau,v}(n)\le C_{\theta(v)}h^{k-1}\exp\bigl(-h\langle n,q-\theta(v)\rangle+h\langle v,n\rangle+C_{\theta(v)}T^2/N\bigr).$$
The exponent is $-h\langle n,\lambda_F(v)\ones\rangle+C_{\theta(v)}T^2/N=-T\lambda_F(v)+C_{\theta(v)}T^2/N$.
The constant of `lem:upper` is
$C_\theta=\max\bigl(e^{k/2}b(\theta')\prod_{i\ge2}\theta_i,\,2q_{\max}\max_i\theta_i\bigr)$. The function
$b$ is continuous on the open set where $\varrho(A'-\operatorname{diag}\theta')<0$, and this set
contains $V_F$ by (A-radii) of `app_torus.tex`. So $v\mapsto C_{\theta(v)}$ is continuous, and it is
bounded on $\mathcal V$.

(b) *Uniform ball.* The set $\mathcal A=\{\alpha^*_F(v):v\in\mathcal V\}$ is compact in
$\Delta_F^\circ$. Fix $\rho_1>0$ such that the closed $2\rho_1$-neighbourhood $\mathcal K'$ of
$\mathcal A$ (in the coordinates $\alpha'$) lies in $\Delta_F^\circ$. On $\mathcal K'$ the matrix
$\Sigma_\alpha^{-1}$ has eigenvalues in $[2c_U,2C_U]$ with $c_U>0$, and $\log C_F$ has bounded
first and second derivatives. Let $U(v)$ be the closed ball of radius $\rho_0\le\rho_1$ around
$\alpha^*_F(v)$, and write $x=\alpha'-\alpha^{*\prime}_F(v)$. The function
$I_F-\langle v,\cdot\rangle$ has gradient $0$ at $\alpha^*_F(v)$ (item 1) and Hessian
$\Sigma_\alpha^{-1}$ (item 3), and $U(v)$ is convex. Hence Taylor's theorem gives, for all
$v\in\mathcal V$ and $\alpha\in U(v)$,
$$c_U|x|^2\le I_F(\alpha)-\langle v,\alpha\rangle-\lambda_F(v)\le C_U|x|^2,\qquad
\Bigl|\log\frac{C_F(\alpha)}{K_F(v)}-\gamma(v)\cdot x\Bigr|\le C_1|x|^2,$$
with $\gamma(v)=\nabla\log C_F(\alpha^*_F(v))$ bounded on $\mathcal V$. Also $\log C_F$ is
$C_3$-Lipschitz on $\mathcal K'$. These are the bounds of the proof of `thm:facemax`, now with
constants that do not depend on $v$.

*Uniform cover outside the ball.* Let
$\mathcal E=\{(v,\beta)\in\mathcal V\times\Delta_F:|\beta'-\alpha^{*\prime}_F(v)|\ge\rho_0\}$, a compact
set. The function $(v,\beta)\mapsto I^{q-v}_F(\beta)-\lambda_F(v)$ is lower semicontinuous, as a
supremum of continuous functions minus a continuous function. By item 1 it is positive on
$\mathcal E$. Hence it is at least $3\eta$ on $\mathcal E$ for some $\eta>0$. For each
$(v_0,\beta_0)\in\mathcal E$ choose $u>0$ with
$\langle q-v_0-A_Fu/u,\beta_0\rangle>\lambda_F(v_0)+\frac52\eta$, and put $\theta=A_Fu/u\in V_F$.
By continuity, $\langle q-v-\theta,\beta\rangle>\lambda_F(v)+2\eta$ on a neighbourhood of
$(v_0,\beta_0)$. Finitely many such neighbourhoods cover $\mathcal E$, with tilts
$\theta_1,\dots,\theta_J\in V_F$. Now let $v\in\mathcal V$ and $\supp n=F$ with
$(v,n/N)\in\mathcal E$, and take $j$ whose neighbourhood contains $(v,n/N)$. Then `lem:upper` with
$\theta=\theta_j$ and (I1) give
$$w_{\tau,v}(n)\le C_{\theta_j}h^{k-1}e^{-h\langle n,q-v-\theta_j\rangle+C_{\theta_j}T^2/N}
\le C\,h^{k-1}e^{-T(\lambda_F(v)+2\eta)}.$$
Put $X(v)=N^{-(k-1)}T^{(k-1)/2}K_F(v)e^{-T\lambda_F(v)}$. Since $K_F$ is bounded below on
$\mathcal V$, the right side is $X(v)\cdot O(T^{(k-1)/2}e^{-2\eta T})$, uniformly in $v$.

*Inside the ball.* By (2.1) and item 6 with $\mathcal K=\mathcal K'$, for $(v,\alpha)$ with
$\alpha=n/N\in U(v)$ and $1\le T\le N^{1/2}$,
$$w_{\tau,v}(n)=X(v)\,\frac{C_F(\alpha)}{K_F(v)}\,e^{-T(I_F(\alpha)-\langle v,\alpha\rangle-\lambda_F(v))}(1+E'),\qquad|E'|\le C_2\Bigl(\frac1T+\frac{T^2}N\Bigr),$$
with $C_2$ independent of $v$. From here the proof of `thm:facemax` applies word for word, with
$\alpha^*_F$ replaced by $\alpha^*_F(v)$ and $\gamma$ by $\gamma(v)$. The upper bound is the maximum
of the concave quadratic $\gamma(v)\cdot x-\frac{c_UT}2|x|^2$, which is at most
$|\gamma(v)|^2/(2c_UT)$. The lower bound uses a lattice point $n^0$ with
$|n^0_i-N\alpha^*_{F,i}(v)|<1$, which exists for $N\ge N_0$ because the entries of $\alpha^*_F(v)$
are bounded below on $\mathcal V$. The location argument gives
$c_UT|\hat x|^2\le C_3|\hat x|+2C_4/T$ for $T\le N^{1/3}$. All constants are uniform on
$\mathcal V$. Finally choose $T_1$ so large that the bound outside the ball is below $X(v)/2$ for
$T\ge T_1$. $\square$

## 3. Lemma 2. The singleton atom

**Lemma 2.** For every state $i$, every $v$ and every $T$ with $hq_{\max}\le\frac12$,
$$M_{\{i\}}(T,v)=\mu_i(1-hq_i)^{N-1}e^{Tv_i}.$$
Hence, with $\lambda_{\{i\}}(v)=q_i-v_i$,
$$\log M_{\{i\}}(T,v)=\log\mu_i-T\lambda_{\{i\}}(v)+\epsilon_i,\qquad|\epsilon_i|\le\frac{q_{\max}T}N+\frac{q_{\max}^2T^2}N,$$
and $T\mapsto\log M_{\{i\}}(T,v)$ is smooth with derivative $-\lambda_{\{i\}}(v)+\epsilon_i'$,
$|\epsilon_i'|\le2q_{\max}(1+q_{\max}T)/N$.

*Proof.* The only path with support $\{i\}$ is $i^N$. It has probability
$\mu_i(1-hq_i)^{N-1}$ and composition $Ne_i$, and $e^{T\langle v,Ne_i\rangle/N}=e^{Tv_i}$. For
$0\le x\le\frac12$ we have $-x-x^2\le\log(1-x)\le-x$. With $x=hq_i$ this gives
$(N-1)\log(1-hq_i)=-Tq_i+hq_i-\vartheta$ with $0\le\vartheta\le Nh^2q_i^2=T^2q_i^2/N$. For the
derivative, $\frac{d}{dT}(N-1)\log(1-hq_i)=-\frac{(N-1)q_i}{N-Tq_i}$, and
$\frac{(N-1)q_i}{N-Tq_i}-q_i=\frac{q_i(Tq_i-1)}{N-Tq_i}$, whose modulus is at most
$2q_i(1+Tq_i)/N$ because $Tq_i\le N/2$. $\square$

So $K_{\{i\}}=\mu_i$ and Lemma 2 is the case $k=1$ of Lemma 1(b), with the error $O(T^2/N)$ only.

## 4. Lemma 3. Suppression at finite $N$

By (A1) the support of $Q$ is symmetric. By `lem:admissible`(c) and (A3), a face is admissible
exactly when it is connected in $G$, and then it satisfies (H). A disconnected face has
$M_F=0$. Note that $S$ is positive semidefinite with $\lambda_{\min}(S)=0$, that $0\le q_i=S_{ii}\le R$,
and that every principal submatrix of $S$ is positive semidefinite with norm at most $R$.

**Lemma 3.** Let $(i,j)$ be an ordered pair of distinct states, and let $(\tau,\delta)$ lie in the
protected rectangle. Let $v=v^{(i,j,\delta)}$ and let $m^*$ be the least score $\Phi_{\tau,v}$ over
the connected faces among $\{i\}$, $\{j\}$, $\{i,j\}$.

(a) Every connected face $F\notin\{\{i\},\{j\},\{i,j\}\}$ has $\Phi_{\tau,v}(F)\ge m^*+\frac34$.

(b) There are $N_0$ and $C$ such that for $N\ge N_0$, uniformly on the rectangle, every face
$F\notin\{\{i\},\{j\},\{i,j\}\}$ has
$$M_F(T,v)\le C(\log N)^{d-1}N^{-3/4}\max\bigl(M_{\{i\}},M_{\{j\}},M_{\{i,j\}}\bigr)(T,v).$$

*Proof.* (a) Let $P=F\cap\{i,j\}$ and $F'=F\setminus\{i,j\}$, so $F'\ne\emptyset$.

*Wholly suppressed faces.* If $P=\emptyset$, then $S_F-\operatorname{diag}v_F=S_F+MI$, so
$\lambda_F(v)\ge M$. Hence $\Phi_{\tau,v}(F)\ge\tau M\ge M/(4R)=1+UR$. Also
$m^*\le\Phi_{\tau,v}(\{j\})=\tau q_j\le UR$. So the gap is at least $1$.

*Mixed faces.* Let $P\ne\emptyset$. Write
$S_F-\operatorname{diag}v_F=\begin{pmatrix}A&B\\B^\top&C\end{pmatrix}$ with
$A=S_P-\operatorname{diag}v_P$ and $C=S_{F'}+MI$. Let $e=\lambda_{\min}(A)$. Then
$|e|\le\lVert S_P\rVert+|\delta|\le4R$, $C\ge MI$ and $\lVert B\rVert\le\lVert S\rVert\le R$. For a
unit vector $(x,y)$,
$$x^\top Ax+2x^\top By+y^\top Cy\ge e|x|^2-2R|x||y|+M|y|^2\ge\frac{e+M}2-\sqrt{\Bigl(\frac{M-e}2\Bigr)^2+R^2}\ge e-\frac{R^2}{M-e},$$
where the middle step is the least eigenvalue of $\begin{pmatrix}e&-R\\-R&M\end{pmatrix}$ and the last
uses $\sqrt{a^2+R^2}\le a+R^2/(2a)$ with $a=(M-e)/2>0$. Since $M-e\ge M-4R=4UR^2$, we get
$\lambda_F(v)\ge e-1/(4U)$. Hence, as $\tau\le U$,
$$\Phi_{\tau,v}(F)\ge|P|-1+|F'|+\tau e-\tfrac14\ge\bigl(|P|-1+\tau e\bigr)+\tfrac34 .$$
If $P$ is $\{i\}$, $\{j\}$ or the edge $\{i,j\}$, then $|P|-1+\tau e=\Phi_{\tau,v}(P)\ge m^*$. If
$P=\{i,j\}$ is not an edge, then $A$ is diagonal, $\tau e$ is the least singleton score, and
$|P|-1+\tau e\ge1+m^*$. In all cases $\Phi_{\tau,v}(F)\ge m^*+\frac34$.

(b) Let $\mathcal V=\{v^{(i,j,\delta)}:|\delta|\le3R\}$, a compact segment. For large $N$ we have
$T=\tau L\in[L/(4R),UL]\subset[T_1,N^{1/3}]$ and $hq_{\max}\le\frac12$. Let $F$ be a connected face
other than the three. If $|F|\ge2$, Lemma 1(a) gives
$M_F\le Ch^{|F|-1}e^{-T\lambda_F(v)+CT^2/N}\le C'T^{|F|-1}N^{-\Phi_{\tau,v}(F)}$, because
$h^{|F|-1}e^{-T\lambda_F(v)}=T^{|F|-1}N^{-(|F|-1)-\tau\lambda_F(v)}$. If $F=\{k\}$ with
$k\notin\{i,j\}$, Lemma 2 gives $M_F\le N^{-\Phi_{\tau,v}(F)}$. For the lower bound, Lemma 2 gives
$M_{\{a\}}\ge\frac12\mu_aN^{-\Phi_{\tau,v}(\{a\})}$ for $a\in\{i,j\}$, and if $\{i,j\}$ is an edge,
Lemma 1(b) gives $M_{\{i,j\}}\ge\frac12\bigl(\min_{\mathcal V}K_{ij}\bigr)N^{-\Phi_{\tau,v}(\{i,j\})}$.
Hence $\max(M_{\{i\}},M_{\{j\}},M_{\{i,j\}})\ge cN^{-m^*}$, and (a) gives the claim with
$T^{d-1}\le(UL)^{d-1}$. Disconnected faces have $M_F=0$. $\square$

Two sharper comparisons inside the three retained faces are needed.

**Lemma 3'.** (i) On the singleton slice $\tau=\tau_0$, $j=1$, $|\delta|\le3R$, if $\{i,1\}$ is an
edge then $\Phi_{\tau_0,v}(\{i,1\})\ge\min(\Phi_{\tau_0,v}(\{i\}),\Phi_{\tau_0,v}(\{1\}))+\frac12$,
and $M_{\{i,1\}}\le C(\log N)^{1/2}N^{-1/2}\max(M_{\{i\}},M_{\{1\}})$.
(ii) On the pair slice $\delta=H$, $1/(4R)\le\tau\le U$, we have
$M_{\{j\}}\le CN^{-1/4}M_{\{i\}}$.

*Proof.* (i) The matrix $S_{\{i,1\}}-\operatorname{diag}v$ has diagonal $(q_i-\delta,q_1)$ and
off-diagonal entries $-\sqrt{w_{i1}}$. So its least eigenvalue is at least
$\min(q_i-\delta,q_1)-\sqrt{w_{i1}}$, and $\tau_0\sqrt{w_{i1}}\le R/(2R)=\frac12$. Hence
$\Phi_{\tau_0,v}(\{i,1\})\ge1-\frac12+\tau_0\min(q_i-\delta,q_1)$. The bound on $M_{\{i,1\}}$ follows
from Lemma 1(b) and Lemma 2 as in Lemma 3(b). (ii) By Lemma 2,
$M_{\{j\}}/M_{\{i\}}=(\mu_j/\mu_i)e^{-T(q_j-q_i+H)}(1+O(T^2/N))$. Since $q_j-q_i+H\ge-R+2R=R$ and
$T\ge L/(4R)$, this is at most $CN^{-1/4}$. $\square$

## 5. Lemma 4. Convexity and the slope of the pair maximum

**Lemma 4 (convexity).** Fix $N$, put $m=N-1$ and $b_N=q_{\max}/N$, and let $F$ be a face and $v$ a
field with $v_a\ge0$ for every $a\in F$ and $M_F(\cdot,v)\not\equiv0$. Then
$$G_F(s)=\log M_F(e^s,v)-m\log(1-b_Ne^s)$$
is convex on $\{s:b_Ne^s<1\}$.

*Proof.* Let $x$ be a path of positive probability with composition $n$, $\supp n=F$. Let $\sigma$ be
its number of switches and $\ell_a$ its number of stays $a\to a$, so that $\sigma+\sum_a\ell_a=m$.
With $a_a=q_a/N\le b_N$ and $T=e^s$, its controlled weight divided by $(1-b_NT)^m$ is
$$c_x\Bigl(\frac T{1-b_NT}\Bigr)^\sigma\prod_{a\in F}\Bigl(\frac{1-a_aT}{1-b_NT}\Bigr)^{\ell_a}e^{T\langle v,n\rangle/N},\qquad
c_x=\mu_{x_1}N^{-\sigma}\prod_{\text{switches}}q_{x_tx_{t+1}}>0 .$$
In the variable $s$, the second derivative of $\log\frac{T}{1-b_NT}$ is $\frac{b_NT}{(1-b_NT)^2}\ge0$,
and that of $\log\frac{1-a_aT}{1-b_NT}$ is $\frac{b_NT}{(1-b_NT)^2}-\frac{a_aT}{(1-a_aT)^2}\ge0$,
because $y\mapsto y/(1-y)^2$ is increasing on $[0,1)$ and $a_a\le b_N$. The second derivative of
$T\langle v,n\rangle/N$ is $T\langle v,n\rangle/N\ge0$, because $v\ge0$ on $F$. So each normalized
path weight is log-convex in $s$. A finite sum of log-convex functions is log-convex, so the
normalized weight of each composition is log-convex. A finite maximum of convex functions is
convex, and $G_F$ is the maximum of the logarithms over the finitely many compositions with
support $F$. $\square$

This is Lemma 1 of `04_C_uniqueness_proof.md`, with the field added. The field term is the only
new factor, and it is the reason for the sign condition. It holds on the pair slice, where
$v_F=(H,0)$ with $H>0$.

**Lemma 4' (slope).** Let $\{i,j\}\in E$, $F=\{i,j\}$, $v=v^{(i,j,H)}$ and $\lambda=\lambda_F(v)$, and
put $\ell(T)=\log M_F(T,v)$. For large $N$ the function $\ell$ has one-sided derivatives at every
$T\in[L/(4R),UL]$, and both are $-\lambda+O(1/L)$ uniformly there.

*Proof.* We never differentiate a remainder. We use secants of the convex function $G=G_F$ and
Taylor's theorem for an explicit comparison function. By Lemma 1(b) with $\mathcal V=\{v\}$,
uniformly for $e^s\in[L/(8R),2UL]$,
$$|G(s)-\mathcal E(s)|\le\frac{C_0}L,\qquad
\mathcal E(s)=-L+\frac s2+\log K_F(v)-\lambda e^s-m\log(1-b_Ne^s),$$
since $1/T+T^2/N=O(1/L)$ on this range. On the same range $1-b_Ne^s\ge\frac12$ and $mb_N\le q_{\max}$,
so $|\mathcal E''(s)|=\bigl|-\lambda e^s+mb_Ne^s/(1-b_Ne^s)^2\bigr|\le C_1L$. Fix
$T\in[L/(4R),UL]$, put $s=\log T$ and $\sigma=1/L$. For large $N$ the points $s\pm\sigma$ lie in the
range. For a convex function the secant slopes increase, so
$$\frac{G(s)-G(s-\sigma)}\sigma\le G'_-(s)\le G'_+(s)\le\frac{G(s+\sigma)-G(s)}\sigma .$$
We replace $G$ by $\mathcal E$ in the two outer secants. This changes each by at most
$2C_0/(L\sigma)=2C_0$. By Taylor's theorem for $\mathcal E$, each secant of $\mathcal E$ differs
from $\mathcal E'(s)$ by at most $C_1L\sigma/2=C_1/2$. Hence $|G'_\pm(s)-\mathcal E'(s)|\le2C_0+C_1/2$.
Now $\ell(e^s)=G(s)+m\log(1-b_Ne^s)$, so
$$\ell'_\pm(T)=\frac1T\Bigl(G'_\pm(s)-\frac{mb_NT}{1-b_NT}\Bigr)=\frac1T\Bigl(\frac12-\lambda T+O(1)\Bigr)=-\lambda+O\Bigl(\frac1L\Bigr),$$
because $T\ge L/(4R)$. $\square$

## 6. Proof of parts (a), (b) and (d). Crossings and the $\tau$ coordinate

Part (d) is Lemma 3(b).

### 6.1 Part (a)

Let $i\ne1$, $\tau=\tau_0$ and $|\delta|\le3R$. By Lemma 3 and Lemma 3'(i), for $N\ge N_0$ every face
other than $\{1\}$ and $\{i\}$ has $M_F\le C(\log N)^{d-1}N^{-1/2}\max(M_{\{1\}},M_{\{i\}})$, uniformly in
$\delta$. So the maximizing support is $\{1\}$ or $\{i\}$, and it is unique unless
$M_{\{1\}}=M_{\{i\}}$. By Lemma 2,
$$\log\frac{M_{\{i\}}}{M_{\{1\}}}=\log\frac{\mu_i}{\mu_1}+(N-1)\log\frac{1-hq_i}{1-hq_1}+T\delta,$$
which is strictly increasing and affine in $\delta$, with slope $T=\tau_0L$. Its zero is the
formula for $x_{i,N}$ in the theorem, and $M_{\{i\}}>M_{\{1\}}$ exactly for $\delta>x_{i,N}$. By the
expansion in the proof of Lemma 2,
$(N-1)\log\frac{1-hq_1}{1-hq_i}=T(q_i-q_1)+h(q_1-q_i)+\vartheta$ with $|\vartheta|\le2q_{\max}^2T^2/N$.
Dividing by $T=\tau_0L=L/(2R)$ gives
$$x_{i,N}=x_i+\frac{2R\log(\mu_1/\mu_i)}{L}+O\Bigl(\frac LN\Bigr).$$
Since $|x_i|\le R$, we have $x_{i,N}\in(-3R,3R)$ for large $N$. This proves (a). Note that the
correction of order $1/\log N$ is present unless $\mu_1=\mu_i$, so the rate $O(1/\log N)$ for the
singleton switches cannot be improved for a general start.

### 6.2 Part (b). The crossing

Let $\{i,j\}\in E$, $F=\{i,j\}$, $\delta=H$ and $v=v^{(i,j,H)}$. Then $\lambda_{\{i\}}(v)=q_i-H$, and
$\lambda_F(v)$ is the least eigenvalue of
$\begin{pmatrix}q_i-H&-\sqrt{w_{ij}}\\-\sqrt{w_{ij}}&q_j\end{pmatrix}$. With $a=H-\Delta_{ij}=q_j-q_i+H$,
$$\lambda_{\{i\}}(v)-\lambda_F(v)=\frac{\sqrt{a^2+4w_{ij}}-a}2=\frac1{t_{ij}}>0,$$
because $1/t_{ij}=2w_{ij}/(\sqrt{a^2+4w_{ij}}+a)$ is the same number. Note that
$R\le a\le3R$, which gives $1/R\le t_{ij}\le U/2$ (since $1/t_{ij}\le\sqrt{w_{ij}}\le R$ and
$1/t_{ij}\ge w_{ij}/(a+\sqrt{w_{ij}})\ge b^2/(4R)$).

By Lemma 3 and Lemma 3'(ii), for $N\ge N_0$ and every $\tau\in[1/(4R),U]$, every face other than
$\{i\}$ and $F$ is smaller than $\max(M_{\{i\}},M_F)$ by a factor $C(\log N)^{d-1}N^{-1/4}$. So the
maximizing support is $\{i\}$ or $F$, and it is unique unless $M_F=M_{\{i\}}$. Put
$$D_N(T)=\log M_F(T,v)-\log M_{\{i\}}(T,v),\qquad\kappa=\log\frac{K_F(v)}{\mu_i},\qquad
\Xi(T)=\frac T{t_{ij}}+\frac12\log T .$$

*The value of $D_N$.* Subtracting Lemma 2 from Lemma 1(b) (with $k=2$, $\mathcal V=\{v\}$) gives,
uniformly for $T\in[L/(8R),2UL]$,
$$D_N(T)=-L+\Xi(T)+\kappa+\rho_N(T),\qquad|\rho_N(T)|\le\frac{C}L .\tag{6.1}$$

*Monotonicity.* For fixed $N$, $M_F(\cdot,v)$ is the maximum of finitely many functions of $T$,
each a positive polynomial times an exponential on the stochastic range. So $\ell=\log M_F$ is
locally Lipschitz, hence absolutely continuous, and its derivative exists almost everywhere and
equals a one-sided derivative there. By Lemma 4' and Lemma 2, at every $T\in[L/(4R),UL]$ both
one-sided derivatives of $D_N$ are
$$-\lambda_F(v)+\lambda_{\{i\}}(v)+O\Bigl(\frac1L\Bigr)=\frac1{t_{ij}}+O\Bigl(\frac1L\Bigr)\ge\frac1{2t_{ij}}$$
for large $N$. Integrating, $D_N(T'')-D_N(T')\ge(T''-T')/(2t_{ij})$ for
$L/(4R)\le T'<T''\le UL$. So $D_N$ is strictly increasing there.

*Signs at the ends.* At $T=L/(4R)$, (6.1) gives $D_N\le-L+L/(4Rt_{ij})+O(\log L)\le-\frac34L+O(\log L)<0$,
since $t_{ij}\ge1/R$. At $T=UL$ it gives $D_N\ge-L+2L+O(1)>0$, since $t_{ij}\le U/2$.

Hence $D_N$ has exactly one zero $T_N$ in $[L/(4R),UL]$. The maximizing support is $\{i\}$ for
$T<T_N$, it is $F$ for $T>T_N$, and both are maximizing supports at $T_N$. So $t_{ij,N}=T_N/L$ is
well defined, and the uniqueness claims of (b) hold.

### 6.3 Part (b). The $\tau$ coordinate

Let $T^\circ$ be the solution of $\Xi(T^\circ)=L-\kappa$. It exists and is unique because $\Xi$ is
increasing from $-\infty$ to $\infty$ on $(0,\infty)$. By (6.1), $\Xi(T_N)=L-\kappa+O(1/L)$, and
$\Xi'\ge1/t_{ij}$. Hence
$$|T_N-T^\circ|\le\frac{Ct_{ij}}L .\tag{6.2}$$
Put $\tau^\circ=T^\circ/L$ and $\varepsilon=\log L/(2L)$. Dividing $\Xi(T^\circ)=L-\kappa$ by $L$ gives
$$\frac{\tau^\circ}{t_{ij}}+\frac{\log L+\log\tau^\circ}{2L}=1-\frac\kappa L .$$
So $\tau^\circ=t_{ij}(1+O(\varepsilon))$ and $\log\tau^\circ=\log t_{ij}+O(\varepsilon)$. Putting this
back,
$$\tau^\circ=t_{ij}\Bigl(1-\varepsilon-\frac{2\kappa+\log t_{ij}}{2L}\Bigr)+O\Bigl(\frac{\log L}{L^2}\Bigr)
=t_{ij}\Bigl(1-\frac{\log L}{2L}\Bigr)+\frac{c_{ij}}L+O\Bigl(\frac{\log L}{L^2}\Bigr),$$
with $c_{ij}=-\frac{t_{ij}}2(\log t_{ij}+2\kappa)$. By (6.2), $t_{ij,N}=\tau^\circ+O(1/L^2)$. This
proves (b).

*Where the sign and the constant $\frac12$ come from.* The term $\frac12\log T$ in $\Xi$ is
$\frac{k_F-k_{\{i\}}}2\log T$ with $k_F-k_{\{i\}}=2-1=1$. It comes from the power $T^{(k-1)/2}$ of
Lemma 1(b). In the proof of `thm:local` that power is the Jacobian $T^{k-1}$ of $t=T\alpha$ in
`lem:continuum` times the Gaussian volume $(2\pi/T)^{(k-1)/2}$ of the Laplace integral over the
$(k-1)$-torus. For a pair this is $T\cdot T^{-1/2}=T^{1/2}$, and a singleton has $T^0$. The
$\frac12$ is therefore $\frac12(k_F-k_G)$ and needs (H) for the pair (compare `rem:half`). Its
sign is positive in $D_N$, so the pair gains $\frac12\log T>0$ over the singleton. The pair then
needs a smaller exponential advantage $e^{T/t_{ij}}$ to make up the cost $N^{-1}$ of the extra
dimension, and it enters earlier than $t_{ij}L$. In the $\tau$ coordinate the gain
$\frac12\log T\approx\frac12\log L$ is divided by the slope $L/t_{ij}$, which gives
$-t_{ij}\log L/(2L)$. The constant $c_{ij}$ collects $\frac12\log t_{ij}$ from $\log T=\log L+\log\tau$
and $\kappa=\log(K_F(v)/\mu_i)$ from the amplitudes. Note that $c_{ij}\ne0$ in general, so the
remainder $O(1/\log N)$ after the $\log\log N$ correction is of exact order $1/\log N$.

## 7. Lemma 5 and the proof of part (c). Reconstruction

**The map $\Psi$ (C-I1).** Given $d=(d_1,\dots,d_d)$ with $d_1=0$ and $t=(t_{ij})_{\{i,j\}\in E}$ with
$t_{ij}>0$, put
$$w_{ij}=\frac{H-d_i+d_j}{t_{ij}}+\frac1{t_{ij}^2},$$
let $B$ be the symmetric matrix with diagonal $d$, entries $-\sqrt{w_{ij}}$ on edges and $0$ on
non-edges, let $\lambda=\lambda_{\min}(B)$ and $\phi$ the positive unit ground vector of $B$, and put
$\Psi(d,t)=-D_\phi^{-1}(B-\lambda I)D_\phi$. At the true coordinates, $w_{ij}$ is the true product
(since $g=1/t_{ij}$ solves $g^2+(H-\Delta_{ij})g-w_{ij}=0$), $B=S-q_1I$, $\lambda=-q_1$ (because
$\lambda_{\min}(S)=0$), $\phi=\sqrt\pi$, and $\Psi(d,t)=-D_{\sqrt\pi}^{-1}SD_{\sqrt\pi}=Q$.

**Lemma 5.** Let $z^0=(d^0,t^0)$ be the true coordinates. There are a neighbourhood $\mathcal N$ of
$z^0$ and constants $0<c\le C$ such that $\Psi$ is real-analytic on $\mathcal N$, $\Psi(z)$ is an
irreducible reversible generator on $G$ for $z\in\mathcal N$, and
$c|z-z^0|\le\lVert\Psi(z)-Q\rVert_2\le C|z-z^0|$ for $z\in\mathcal N$.

*Proof.* At $z^0$ every $w_{ij}$ is positive, so on a neighbourhood the map $z\mapsto w$ is
real-analytic with positive values, and so is $z\mapsto B$. The matrix $-B$ is an irreducible
Metzler matrix (its off-diagonal pattern is the connected graph $G$), so $\lambda_{\min}(B)$ is a simple
eigenvalue with a positive eigenvector. By the implicit function theorem $\lambda$ and $\phi$ are
real-analytic near $z^0$, and $\phi>0$. Hence $\Psi$ is real-analytic. The matrix $\Psi(z)$ has
off-diagonal entries $\sqrt{w_{ij}}\phi_j/\phi_i>0$ exactly on the edges, and
$\Psi(z)\ones=-D_\phi^{-1}(B-\lambda I)\phi=0$. It is reversible with respect to $\phi\circ\phi$, since
$\phi_i^2\sqrt{w_{ij}}\phi_j/\phi_i=\phi_i\phi_j\sqrt{w_{ij}}$ is symmetric. This gives the upper
Lipschitz bound. For the lower bound, the map $\Psi$ has a real-analytic left inverse on the
reversible generators on $G$ near $Q$, namely $Q'\mapsto(d',t')$ with $d'_i=q'_i-q'_1$ and $t'_{ij}$ given
by the formula of Section 1 with $w'_{ij}=q'_{ij}q'_{ji}$. Indeed $\Psi(z)$ has exit rates
$q_i=d_i-\lambda$ and products $w_{ij}$, and the formula for $t$ inverts the formula for $w$. A
Lipschitz left inverse gives $|z-z^0|\le C'\lVert\Psi(z)-Q\rVert_2$. $\square$

*Proof of (c).* By (a), $|d_{i,N}-d^0_i|=O(1/L)$. By (b),
$|t_{ij,N}-t_{ij}|=t_{ij}\log L/(2L)+O(1/L)$. Hence $z_N=(d_N,t_N)\to z^0$, $z_N\in\mathcal N$ for large $N$,
and $|z_N-z^0|$ lies between two positive multiples of $\log L/L$. Lemma 5 gives
$\lVert Q_N-Q\rVert_2\asymp\log\log N/\log N$. After the correction,
$$\frac{t_{ij,N}}{1-\varepsilon_N}=\frac{t_{ij}(1-\varepsilon_N)+c_{ij}/L+O(\log L/L^2)}{1-\varepsilon_N}=t_{ij}+O\Bigl(\frac1L\Bigr),$$
so $|\widetilde z_N-z^0|=O(1/L)$ and $\lVert\widetilde Q_N-Q\rVert_2=O(1/\log N)$. $\square$

The rate $1/\log N$ after the correction is again of exact order in general, because $c_{ij}$ and
$2R\log(\mu_1/\mu_i)$ are nonzero in general and depend on $\mu$, which the design does not observe.
Remark 8.3 shows how a second singleton slice removes the start from the $x$ coordinates.

## 8. Remarks

**8.1 Dependence of the threshold.** $N_0$ and the implied constants depend on $(Q,\mu)$ through
finitely many continuous quantities. These are $\min_i\mu_i$, the constants $K_{ij}(v^{(i,j,H)})$, the tilt
constants $C_\theta$ on the segments of fields, the radius $\rho_0$, the gap $\eta$ and the Laplace
constants of `thm:local` on $\mathcal K'$, and $q_{\max}$. This is the list that route T5-B must make
uniform. We do not claim uniformity here. In particular the term $2R\log(\mu_1/\mu_i)/\log N$ in
part (a) is unbounded as $\mu_i\to0$, in line with the counterexample over all starts in Section 5
of the outline.

**8.2 What was used from the draft.** The proof uses `lem:runs`, `lem:continuum`, `lem:admissible`,
`prop:rate`, `prop:constant`, `lem:perron`, `lem:torus`, `lem:laplace`, `thm:local`, `lem:discrete`
and `lem:upper`, all at the fixed chain and with the proofs in the draft. It re-proves `thm:facemax`
with the field (Lemma 1), adapts the convexity lemma of `04_C_uniqueness_proof.md` (Lemma 4), and
replaces the crossing argument of `thm:crossing` by Sections 6.2 and 6.3. That theorem does not
prove uniqueness of the zero, and the convexity lemma supplies it on the pair slice. On the
singleton slice no convexity is needed, since the comparison is exact and affine in $\delta$.

**8.3 Removing the start from the singleton switches.** By the exact formula in (a),
$\tau_0Lx_{i,N}(\tau_0)-\tau_0'Lx_{i,N}(\tau_0')$ does not involve $\mu$ for two slices
$\tau_0\ne\tau_0'$ at which the singleton comparison is protected. Solving the two exact equations
gives $q_i-q_1$ up to $O(L/N)$. This is an option for the design and is not part of Theorem 5(a).

**8.4 Units.** Under $(Q,v,\tau)\mapsto(cQ,cv,\tau/c)$ the time $T$ and the products $Tq$ are
unchanged. So the size $T^2q_{\max}^2/N$ of the discretization error at the crossing does not depend
on the units, and the numerical check below cannot be made easier by rescaling.

## 9. Numerical check

**Example.** The path $1-2-3$ with $q_{12}=1$, $q_{21}=2$, $q_{23}=1$, $q_{32}=1$. It is reversible
with $\pi=(\frac12,\frac14,\frac14)$, and $q=(1,3,1)$. Then $\lVert S\rVert_2=4$, and we take $R=4$
and $b=1$. So $H=8$, $\tau_0=\frac18$, $U=32$ and $M=2064$. The start is $\mu=(0.5,0.3,0.2)$. For
each retained ordered edge the script computes the exact face maxima $M_{\{i\}}$ (Lemma 2) and
$M_{\{i,j\}}$ (the killed two-state run expansion of `lem:runs`, maximized over all compositions)
and solves $M_{\{i,j\}}=M_{\{i\}}$ in $\tau$ to $10^{-13}$. For $N\le2\cdot10^4$ the maximum over
compositions is a full scan. For larger $N$ a strided scan locates the peak and the maximum is then
taken over every composition in a window of $6N/4000$ around it. At $N=10^5$ a full scan gives the
same maximum and the same maximizer for all four pairs. The constant $K_{ij}(v)$ is computed by
(2.2) and, independently, from the Perron vectors and $\det\Sigma=2ab/(a+b)^3$ (`lem:forest`), and
the two agree to $10^{-10}$. The columns are the exact entry time $\tau_N=t_{ij,N}$, the corrected
first-order value $t_{ij}(1-\varepsilon_N)$ with $\varepsilon_N=\log\log N/(2\log N)$, the scaled
residual $(\tau_N-t_{ij}(1-\varepsilon_N))\log N$, which part (b) says tends to $c_{ij}$, the root
$\tau^\circ$ of the crossing equation $T/t_{ij}+\frac12\log T=\log N-\log(K_{ij}/\mu_i)$, the
residual $(\tau_N-\tau^\circ)(\log N)^2$, which (6.2) says is bounded, and the error of Lemma 1(b)
for the pair at the crossing, $\log M_{\{i,j\}}-(-L+\frac12\log T+\log K_{ij}-T\lambda_{ij})$.

| pair $(i,j)$, $t_{ij}$, $c_{ij}$ | $N$ | $\tau_N$ exact | $t_{ij}(1-\varepsilon_N)$ | $(\tau_N-t_{ij}(1-\varepsilon_N))L$ | $\tau^\circ$ | $(\tau_N-\tau^\circ)L^2$ | Lemma 1 error |
|---|---|---|---|---|---|---|---|
| $(1,2)$, $5.0981$, $-14.783$ | $10^3$ | 2.531203 | 4.384909 | $-12.805$ | 2.506800 | $1.164$ | $-0.1749$ |
| | $10^4$ | 3.009146 | 4.483582 | $-13.580$ | 3.023165 | $-1.189$ | $-0.0081$ |
| | $10^5$ | 3.350785 | 4.557076 | $-13.888$ | 3.365022 | $-1.887$ | $0.0272$ |
| | $10^6$ | 3.597110 | 4.613603 | $-14.043$ | 3.607393 | $-1.963$ | $0.0281$ |
| $(2,1)$, $3.1583$, $-7.142$ | $10^3$ | 1.783680 | 2.716498 | $-6.444$ | 1.809843 | $-1.249$ | $-0.5983$ |
| | $10^4$ | 2.062656 | 2.777627 | $-6.585$ | 2.074256 | $-0.984$ | $-0.1207$ |
| | $10^5$ | 2.243500 | 2.823157 | $-6.674$ | 2.249345 | $-0.775$ | $-0.0067$ |
| | $10^6$ | 2.370237 | 2.858176 | $-6.741$ | 2.373842 | $-0.688$ | $0.0118$ |
| $(2,3)$, $6.1623$, $-16.253$ | $10^3$ | 3.134128 | 5.300240 | $-14.963$ | 3.234849 | $-4.806$ | $-2.0094$ |
| | $10^4$ | 3.773921 | 5.419511 | $-15.156$ | 3.815261 | $-3.507$ | $-0.4698$ |
| | $10^5$ | 4.179605 | 5.508346 | $-15.298$ | 4.199279 | $-2.608$ | $-0.0638$ |
| | $10^6$ | 4.459981 | 5.576673 | $-15.428$ | 4.471763 | $-2.249$ | $0.0108$ |
| $(3,2)$, $10.0990$, $-36.328$ | $10^3$ | 4.187823 | 8.686273 | $-31.074$ | 4.088345 | $4.747$ | $-0.4774$ |
| | $10^4$ | 5.273665 | 8.881740 | $-33.232$ | 5.291833 | $-1.541$ | $-0.0952$ |
| | $10^5$ | 6.065820 | 9.027326 | $-34.096$ | 6.093531 | $-3.673$ | $0.0102$ |
| | $10^6$ | 6.640968 | 9.139304 | $-34.516$ | 6.661882 | $-3.992$ | $0.0261$ |

In every case $D_N$ was increasing on a 7-point grid from $\tau=1/(4R)$ to $1.2t_{ij}$, as Section
6.2 predicts. A full dynamic program over all $\binom{302}2$ compositions of the three states at
$N=300$ (pair $(1,2)$, exact entry $\tau_N=2.21706$) gives the global maximizing support $\{1\}$ at
$0.5\tau_N$ and $0.99\tau_N$, and $\{1,2\}$ at $1.01\tau_N$ and $1.2\tau_N$, with $\{1,2\}$ or $\{1\}$
as runner-up. No face containing the suppressed state comes close.

The singleton switches at $\tau_0=\frac18$, exact formula against
$x_i+2R\log(\mu_1/\mu_i)/\log N$, with $x_2=2$ and $x_3=0$.

| $N$ | $x_{2,N}$ | prediction | $x_{3,N}$ | prediction |
|---|---|---|---|---|
| $10^3$ | 2.593054 | 2.591597 | 1.061173 | 1.061173 |
| $10^4$ | 2.443958 | 2.443697 | 0.795880 | 0.795880 |
| $10^5$ | 2.354996 | 2.354958 | 0.636704 | 0.636704 |
| $10^6$ | 2.295803 | 2.295798 | 0.530587 | 0.530587 |

(For $i=3$ we have $q_3=q_1$, so the $O(L/N)$ term vanishes and the prediction is exact.)

**Reading of the numbers.** The sign and the coefficient $\frac12$ are confirmed in the sharp form
that the proof gives. The residual $(\tau_N-\tau^\circ)L^2$ stays bounded over three decades, so the
crossing equation with the $\frac12\log T$ term places the exact entry time to $O(1/L^2)$ in $\tau$.
With $\frac12\log T$ replaced by $0$ or by $\log T$ the residual would grow like $L\log L$. The
scaled residual $(\tau_N-t_{ij}(1-\varepsilon_N))L$ drifts slowly toward $c_{ij}$ (for $(1,2)$ from
$-12.8$ to $-14.0$ against $-14.8$), at the rate $O(\log L/L)$ that part (b) allows. The table also
shows that the term $c_{ij}/\log N$ is large in practice. In this example $\log(K_{ij}/\mu_i)$ is
between $1.7$ and $2.5$ and the controlled quasi-ergodic law $\alpha^*_{ij}(v)$ puts only 1 to 5 percent of the time in state $j$,
so at $N=10^6$ the corrected first-order value $t_{ij}(1-\varepsilon_N)$ still overshoots the exact
entry time by 20 to 40 percent, while $\tau^\circ$ is within 0.4 percent. So $t_{ij}(1-\varepsilon_N)$
is the right asymptotic statement, but a finite-$N$ inversion should solve the crossing equation.
The error of Lemma 1(b) at the crossing is $0.01$ to $0.03$ at $N=10^6$, of the size $1/T$.

## Status

**Status: proved.** Theorem 5(a), parts (a) to (d), is proved for a fixed chain and a fixed start
under (A1) to (A3). The proof uses `lem:runs`, `lem:continuum`, `lem:admissible`, `prop:rate`,
`prop:constant`, `lem:perron`, `lem:torus`, `lem:laplace`, `thm:local`, `lem:discrete` and
`lem:upper` exactly as proved in the draft at `6add913`, and Section 2.2 checks that none of them
needs $q-v\ge0$. The correction is $t_{ij,N}=t_{ij}(1-\log\log N/(2\log N))+c_{ij}/\log N+O(\log\log N/(\log N)^2)$
with the minus sign and the coefficient $\frac12$ derived from the power $T^{1/2}$ of the pair, and
an explicit $c_{ij}$ that is nonzero in general. The reconstruction error is of exact order
$\log\log N/\log N$ before the correction and $O(1/\log N)$ after it. The threshold $N_0$ is not
made explicit and is not uniform over the class (that is route T5-B). The numerical check on a
3-state reversible chain at $N=10^3$ to $10^6$ agrees with the crossing equation to $O(1/(\log N)^2)$
in $\tau$.
