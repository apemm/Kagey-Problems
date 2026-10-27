# 12. Audit of 04_exposure_queues.md

Date: 26 October 2026. This is a read-only check of `04_exposure_queues.md` against Paper F
(`kagey-problems/problem131/paperF`, the sec_*.tex files as they stand today) and the cited sources.
Nothing outside this file was edited. My own script and its output are in a scratch folder outside
the repo; §5 describes what they do.

## Verdicts

| Item | Verdict |
|---|---|
| Q0 (cyclic lemma) | proved as written |
| Q1 ((LR), (SPAN), constant) | proved as written; the citations check out, with the numbering caveats in §1 |
| Q2 ((LD) for the cycle) | proved as written |
| Claim A (`lem:second-bigjump` with $L\ge cm$) | **true, and the proof is complete**: every dependency has been audited (§2) |
| Q3 ((LD2) for the cycle) | proved (Claims B, C and the assembly are checked in §2) |
| E1 (imbalance scale) | correct after a stated restriction: for a random-time start the uniform local statement and the bound $C/B_N$ hold only for $1\le k<N$ unless $\alpha>\varphi$ |
| E2 ($P(N-A_N<\varepsilon N)$) | proved; one citation needs fixing (the last $\delta N$ points come from `thm:bigjump`(b), not (c)) |
| E3 (no switch) | proved as written |
| E4 (fresh vs random factor) | proved as written for the queue, where the indices are equal; with unequal indices use $\alpha_\sigma$ in each term |
| E5 (golden ratio) | proved as written; all four corrections to the plan are right |
| E6 (three modes) | conditional, as the note says (needs strict log-convexity of $f_C$) |

---

## 1. Q0 and Q1

**Q0.** Starting from an empty system, $V_1=W_1$, and while $V_{t-1}\ge1$ we have
$V_t=V_{t-1}-1+W_t$. So $C=\inf\{t:U_t-t=-1\}$. The walk $U_t-t$ is downward skip-free, and the
hitting-time theorem gives $P(C=n)=P(U_n=n-1)/n$. My DP on the workload agrees with this formula to
$10^{-11}$ relative for $n=5$, 50 and 300 (§5).

**Q1, my derivation.** Put $x=n-1$ and $L=x-n\rho=(1-\rho)n-1$, and split $P(U_n=x)$ by the number
of summands above $\delta n$.
- *Two or more:* at most $n^2T_W(\delta n)\sup_{m>\delta n}f(m)\le C_\delta n^2T(n)f(n)$. Relative
  to $nf(n)$ this is $C\,nT(n)\to0$.
- *Exactly one:* $n\sum_yP(U_{n-1}=y,\max\le\delta n)f(x-y)$.
  - On $|y-(n-1)\rho|\le\varepsilon n$, $f(x-y)=f(L)(1+O(\omega(\varepsilon)))$. The truncated
    event has probability $1-o(1)$, since $P(\max>\delta n)\le nT(\delta n)\to0$ and the weak law
    holds.
  - Off that range, the bounds $C_\delta f(n)$ (when $y$ is large) and $Cf(L)$ by Potter (when $y$
    is small) are each multiplied by a probability that is $o(1)$.
  - No local limit theorem is used, so (SPAN) for $W$ is not needed.
- *None:* Bennett's inequality (the halving is harmless and not needed) gives a bound
  $n^{-(\alpha-1)(1-\rho)/(2\delta)+o(1)}$. This is $o(n^{-\alpha-1})$ under the stated condition on
  $\delta$, and only $o(n^{-\alpha})$ is needed.

So $P(U_n=n-1)\sim nf_W((1-\rho)n)$, and
$$f_C(n)\sim\lambda f_\sigma((1-\rho)n)\sim\alpha\lambda c_\sigma(1-\rho)^{-\alpha-1}n^{-\alpha-1}.$$
Karamata gives the tail. The check $E[C]T_W((1-\rho)n)=(1-\rho)^{-1}(1-\rho)^{-\alpha}T_W(n)$ is
consistent. (LR) for $C$ follows with the same $\alpha$. (SPAN) follows from $f_C(1)=1-\lambda>0$
and $f_C(n)>0$ for all large $n$.

**Kortchemski.** I checked arXiv 1205.3145v4 (Sept. 2013). The published AIHP numbering was not
checked.
- *Hypothesis* $(H_\theta)$: $0<m<1$, and $\mu_n=L(n)/n^{1+\theta}$ for all $n\ge1$, with $L$ slowly
  varying and $\theta>1$ (any $\theta>1$, not only $\theta<2$).
- *Eq. (14):* $P_\mu(|\tau|=n)=n^{-1}P(W_n=-1)\sim L(n)/(\gamma n)^{1+\theta}$, with $\gamma=1-m$.
  The proof uses Denisov–Dieker–Shneer Theorem 9.1.
- *Fit with the slotted model:* the offspring law is $W$, with $\mu_0=1-\lambda$,
  $\mu_n=\lambda f_\sigma(n)$, $m=\rho$ and $\theta=\alpha$. $(H_\theta)$(ii) is exactly
  regular variation of $f_W$, which is (LR) for $W$. So (14) is Q1 verbatim, including slowly
  varying $L$, and the note's description is accurate.

**Janson.** I checked arXiv 1112.0510v1. The published Probab. Surveys numbering was not checked.
- *Remark 18.34*, the tree case of Theorem 18.33(ii), states
  $Z_n\sim c(1-\nu)^{-\beta}\Phi(1)^{n-1}n^{-\beta}\sim(1-\nu)^{-\beta}\Phi(1)^{n-1}w_n$.
- *Hypotheses:* $w_k\sim ck^{-\beta}$ with $\beta>2$, a constant $c$, and $\nu<1$.
- *Fit with the slotted model:* for probability weights, $\Phi(1)=1$, $Z_n=P(|T|=n)$, $\nu=\rho$
  and $\beta=\alpha+1$. This gives Q1 when $f_\sigma(n)\sim\alpha c_\sigma n^{-\alpha-1}$ (the note's
  constant case, including zeta). It does not cover a nonconstant slowly varying factor, and the
  note says this correctly ("for $w_k\sim ck^{-\beta}$").
- Janson's (17.38) gives the same constant by singularity analysis under an analytic hypothesis.

**Denisov–Shneer (Queueing Syst. 64 (2010) 383–393).** I could not reach the full text. The abstract
says it derives global and local busy-period asymptotics for M/G/1 with subexponential service,
from the explicit joint law of the number served and the busy-period length. It is continuous
time, so it does not cover the slotted cycle verbatim. The slotted case is already covered exactly
by Kortchemski (14). Their arXiv paper 0712.0728 (first-passage times) is tail-only: Theorem 2.2,
$P(\nu_x>n)\sim E\nu_x\,P(X_1>na)$, and Corollary 2.1 for the M/G/1 busy period. The note's
instruction to read the 2010 paper before saying anything about M/G/1 stands.

## 2. Q2, Claim A, Q3

**Q2.** With $W'=W+1$ (support $\{1,2,\dots\}$, $f_{W'}(1)=1-\lambda>0$, and (SPAN), (LR), (LD2)
inherited from $\sigma$) and $V_m=f_{W'}^{*m}$, we have $\varphi(n)=nf_C(n)=V_n(2n-1)$.
- The identity
  $\varphi(n+1)-\varphi(n)=\delta V_n(2n+1)-\nabla V_n(2n+1)-\nabla V_n(2n)$ is exact.
- `lem:diff-bigjump` requires only $L\ge Ka(m)$. I read its proof in sec_modeproofs.tex, and no
  $L\ge m\mu$ is used, so it applies at $L=(1-\rho)n\pm O(1)$.
- The leading terms give $f(L)+(\alpha+1)\frac{nf(L)}{L}(\mu'-2)=-\alpha f(L)$, using
  $\mu'-2=-(1-\rho)$. The error is $O(\varepsilon)f(L)$, with no cancellation of leading order.
- Then $\Delta f_C=\Delta\varphi/(n+1)-\varphi/(n(n+1))=-(\alpha+1+o(1))f_C/n$. **Proved.**

**Claim A, my derivation of the critical step.** In the proof of `lem:second-bigjump`, the
hypothesis $L\ge m\mu$ enters only through the no-giant term. That term is bounded by
$Ca(m)^{-2}(mT(w))^{L/(8w)}$, and it has to be $o(mf(L)/L^2)$ uniformly in $m$.
- Under $L\ge cm$: $mT(\delta L)\le c^{-1}L\,C_\delta T(L)\le C_{\delta,c}L^{1-\alpha+\varepsilon'}$
  and $a(m)^{-2}\le a(1)^{-2}$. So the term is at most
  $CL^{-(\alpha-1-\varepsilon')/(16\delta)}$, against the target
  $mf(L)/L^2\ge f(L)/L^2\ge L^{-\alpha-3-\varepsilon'}$. Choosing $\delta$ small (now depending on
  $c$) closes it.
- With only $L\ge Ka(m)$ the comparison would be $a(m)^{-2}\,r^{-\cdots}$ against
  $a(m)^{-3}r^{-\alpha-2}$, which fails for large $m$. This is why some linear lower bound on $L$ is
  needed.

**Claim A, every other step of the proof.**
- *Main sum:* $|\nabla^2f(n-z)|\le C_\delta f(L)/L^2$ for $n-z\ge\delta L$, by (LD2), with total
  mass at most 1 per $i$. This does not use $m$.
- *First boundary term:* the factor $mT(L)L/a(m)\le Cr^{1-\alpha+\varepsilon'}\le C$ comes from
  `eq:potter-m` with $r=L/a(m)\ge1$. This does not use $L\ge m\mu$.
- *Second boundary term:* the proof of the first bound of `lem:diff-bigjump` is applied to $h_i$ at
  deviation at least $(1-2\delta)L$. It needs only $r\to\infty$, which follows from $L\ge cm$, since
  then $a(m)=o(L)$. The final factor $mLf(L)\le CmT(L)\le C$ also comes from `eq:potter-m`.
- *Sub-lemmas:* `lem:trunc-local`(a),(b) need only $mT(w)\le1$, which holds for $L\ge L_0(c)$.
  `lem:truncated` holds for all $m$, $w$ and $z$. `lem:stable`(iii) holds for all $m$ and
  $j-m\mu\ge1$. None of them uses $L\ge m\mu$.

So the bound holds for $L\ge\max(K_1a(m),L_0,cm)$, with constants depending on $c$. The note's
caveat ("not re-audited") is resolved: **Claim A is true and the proof is complete.**

**Claim B.**
- *Range $x\le L/2$:* bracket at most $x\cdot Cmf(L)/L^2$ by A at deviation at least $L/2$ (apply A
  with $c/2$). Summed against $f(x)$ this is at most $C\mu'mf(L)/L^2\le Cf(L)/L$.
- *The term $\nabla V_m(n)T(L/2)$:* $O(f(L)/L\cdot mT(L))=o(f(L)/L)$.
- *Range $x>L/2$:* summation by parts gives
  $\sum[f(x-1)-f(x)]V_m(n-x)\le Cf(L)/L$, by (LD) for $f_{W'}$ (from (LD2) via `lem:ld2`). The
  boundary term is $f(L/2)V_m(n-L/2)\le Cf(L)\cdot mf(L)$, and $mLf(L)\le CLT(L)/c\to0$.
- **Correct.**

**Claim C.**
- $\delta^2V_m=f*\delta V_m-\delta V_m$, since $\delta V_{m+1}=f*\delta V_m$.
- *Range $x\le L/2$:* handled by B.
- *Tail term:* $O(f(L)T(L))=o(f(L)/L)$.
- *Rest:* it equals $E[\gamma(S_m+X)-\gamma(S_m)]$ with $\gamma(y)=f(n-y)\mathbf 1\{n-y>L/2\}$.
  - Both arguments in range: $\le\mu'\sup_{>L/2}|\nabla f|\le Cf(L)/L$.
  - Only $S_m$ in range: $Cf(L)\sum_kT(k)V_m(n-L/2-k)$. Split at $k=L/4$ to get
    $\le C(mf(L)+T(L))\le CT(L)=o(1/L)$.
  - Since $X\ge1$, the case where only $S_m+X$ is in range cannot occur.
- **Correct.**

**Assembly.** $\Delta^2\varphi=(\delta E_x^2+(E_x^2-1))^2V_n$ expands into one $\delta^2$ term, two
$\nabla\delta$ terms and four $\nabla^2$ terms. They sit at indices up to $n+2$ and arguments up to
$2n+3$, all with deviation $(1-\rho)n+O(1)\ge cm$ for $c=(1-\rho)/2$. Each is $O(f(L)/L)$, using
$m\,f(L)/L^2\le Cf(L)/L$ for the $\nabla^2$ terms. The product rule with $g=1/n$ gives
$\Delta^2(\varphi g)=O(f/n^2)$. **Q3 is proved.**

## 3. Design corollaries

**E1** (`thm:bulk`(a),(b); `thm:preparation`(b); `cor:stationary`).
- *Fresh start:* the statement matches `thm:bulk` exactly. The profile
  $W_\theta=(1-p)\theta_+Z_+-p\theta_-Z_-$ matches `eq:profile`.
- *Random-time start, interior:* `cor:stationary` gives the bulk criterion, so
  `thm:preparation`(b) gives the uniform statement on $1\le k<N$.
- *Random-time start, endpoints:* the uniform statement over all $0\le k\le N$ holds only if
  $B_nP(D\ge n)\to0$, that is, $B_NQ_\pm(N)\to0$. Since $B_NQ_\pm(N)\in RV_{1/\alpha+1-\alpha}$, this
  holds for $\alpha>\varphi$ and fails for $\alpha<\varphi$.
  - So for $\alpha<\varphi$ the bound "$P(A_N=k)\le C/B_N$ for every $k$" is **false** at
    $k\in\{0,N\}$. E5 itself says that those atoms beat every interior value.
  - The sentence "the no-switch atoms do not change this" is right only for the distributional
    limit, since $Q_\pm(N)\to0$.
- *Restriction:* for a random-time start, state the local form and the $C/B_N$ bound on
  $1\le k<N$, or on all $k$ when $\alpha>\varphi$.

**E2** (`thm:bigjump`(b) additive form; `cor:infinite-density`; `cor:stationary`(a),(b)).
- *Interval and zone:* $[(1-\varepsilon)N,N]$ lies in the zone for $\varepsilon<1-p$, since
  $\lambda_NB_N=o(N)$.
- *Additive errors:* they sum to $o(\sum\widehat G_N)=o(NT_+(N))$, because
  $\widehat G_N\le CT_+(N)$ when $L_k\ge N/2$.
- *Integral:* I recomputed $\int_{1-\varepsilon}^1I_+\,dv$. With $\ell=(v-p)/(1-p)$, $dv=(1-p)\,d\ell$
  and $(1-p)/\mu_-=1/s$, it equals
  $\frac{1-p}{\mu_-}[-(1-\ell)\ell^{-\alpha}]_{\ell_\varepsilon}^1=\varepsilon\ell_\varepsilon^{-\alpha}/\mu_-$.
- *Random-time start:* $\int\ell^{-\alpha}/\mu_-\,dv=(\ell_\varepsilon^{1-\alpha}-1)/(s(\alpha-1))$, and
  adding the atom $Q_+(N)\sim NT_+(N)/(s(\alpha-1))$ gives exactly the note's
  $\ell_\varepsilon^{1-\alpha}/(s(\alpha-1))$.
  - So the added term is the initial-run term plus the atom, not a single term. The formula is
    right.
  - The ratio form of `cor:stationary`(b) on $k<N$ plus uniform convergence on compacts of $(p,1)$
    is enough for the sum.
- *Citation slip:* `thm:bigjump`(c) is stated for windows $\delta_NN$ with $\delta_N\to0$. The bound
  $C\delta NT_+(N)$ for the last $\delta N$ points with $\delta$ fixed should instead cite the
  additive form of (b), with $G_N,\widehat G_N\le CT_+(N)$ there. This is not a gap.

**E3** (`prop:fresh-identity`, `prop:first-run`, `cor:stationary`(a)). These are exact identities:
fresh plus gives $T_+(N)$, and the random start gives $Q_+(N)+Q_-(N)$, with
$Q_\sigma\sim NT_\sigma(N)/(s(\alpha_\sigma-1))$. In the queue, the random-start initial run is the
residual of the current cycle in the alternating renewal process, with law $T_\sigma/s$, as F
requires. **Proved.**

**E4.** $(Q_++Q_-)/T_+\sim\frac{N}{s(\alpha-1)}(1+T_-/T_+)$. Both arms share the service law, so
$\alpha_+=\alpha_-$ and the formula is exact. In general the second term carries $\alpha_-$.
**Proved.** My recomputation agrees exactly with the note (§5).

**E5** (`thm:mode`(c),(d)).
- *Hypotheses:* (RV), (SPAN), and the bulk criterion, which holds for the stationary start by
  `cor:stationary`.
- *Equal indices:* endpoint for $\alpha<\varphi$, interior for $\alpha>\varphi$, for all large $N$.
- *Unequal indices:* per arm, $\alpha_\sigma-1<1/\alpha_*$, away from equality.
- *The four corrections:*
  1. Not an iff at $\alpha=\varphi$. For the queue, $T_\pm\sim c_\pm n^{-\alpha}$ with no slowly
     varying factor, so at $\alpha=\varphi$ the ratio $B_NQ_\sigma/H_N$ tends to a finite constant.
     F's $\mathcal C(\varphi)=0.776$ is for $T(n)=n^{-\alpha}$ exactly, and the queue constant is not
     computed.
  2. The theorem compares each atom separately with $P^{\max}_N$.
  3. The result holds for all large $N$, not every $N$.
  4. The per-arm rule with unequal indices.

  All four are accurate.
- *Control-only extension:* $\nu_-=T_-/\mu_-$ and $\nu_+=0$ give
  $Q_-=\mu_-^{-1}\sum_{d\ge N}T_-(d)\in RV_{-(\alpha-1)}$ and $Q_+=0$. The bulk criterion holds,
  since $B_nT_-(n)\to0$, and `thm:mode`(c) gives the same threshold. **Correct.**
- *Fresh start:* the mode is interior (last sentence of (d)). **Correct.**
- *Trends:* the observed atom-to-interior ratios $3.28\to4.39$ (factor 1.34) and
  $0.291\to0.220$ (factor 0.76) over $N=1000\to4000$ are consistent with
  $N^{1-\alpha+1/\alpha}$ (factors 1.26 and 0.71).

**E6.** `thm:mode-count` and `cor:logconvex-three` need (SPAN), (LR), (LD2), (EQ) and strict
log-convexity of $f_\pm$. (LD2) is now closed by §2. Log-convexity of the total-progeny law is
unproved, and the note says so. **Conditional.**

Not audited: the AFK transfer to geometric numbers of cycles (§1 of the note) and the positioning
literature (§4).

## 4. Smallest open items after this audit

1. Restate E1 for the random-time start (restriction above).
2. In E2, cite the additive form of `thm:bigjump`(b) for the last $\delta N$ points, not (c).
3. Check the published numbering of Kortchemski eq. (14) (AIHP 2015) and Janson Rem. 18.34
   (Probab. Surveys 2012); both were verified on arXiv versions only.
4. E6 still needs log-convexity (or monotone $u_-$) for total-progeny laws.

## 5. Independent recomputation

Script `check.py`, written from scratch (it does not import 04_cycle_law.py) and run with `py -I`.
It covers $\alpha=1.5$ with zeta($\alpha+1$) service.
- **Workload DP versus the cyclic lemma.** The DP iterates
  $V_t=\max(V_{t-1}-1,0)+W_t$ with an FFT convolution. The cyclic lemma uses
  $P(U_n=n-1)/n$ from FFT powers of $\hat f_W$. Relative differences are $5\times10^{-12}$,
  $4\times10^{-12}$ and $1\times10^{-12}$ at $n=5$, 50 and 300.
- **Constant.** $f_C/\text{prediction}$ is 0.99851 and 0.99963 for $\rho=0.4$, and 0.98889 and
  0.99717 for $\rho=0.6$, at $n=2^{12}$ and $2^{14}$. The note reports 0.9996 and 0.9972 at
  $2^{14}$.
- **First difference.** $n\Delta f_C/f_C$ is $-2.4996$ ($\rho=0.4$) and $-2.4971$ ($\rho=0.6$) at
  $n=2^{14}$, against $-2.5$.
- **Second difference.** $n^2\Delta^2f_C/f_C$ is sensitive to FFT aliasing. With FFT length $256n$
  it is 8.674, 8.715, 8.743 and 8.777 at $n=1024$, 2048, 4096 and 8192. With length $64n$ the large-$n$
  values drift upward (9.94 at 8192), which is an artifact. The result is consistent with $8.75$
  to the precision available.
- **No-switch ratio.** Here $\rho_\pm=0.6/0.4$, $T_\pm$ come from the DP up to $N=4000$, and
  $\sum_{d\ge N}T=E[C]-\sum_{d<N}T$ exactly. The exact ratio $(Q_++Q_-)/T_+$ is 607.37, 1203.82 and
  2396.24 against the asymptotic 598.80, 1195.00 and 2387.28 at $N=1000$, 2000 and 4000. This is
  identical to the note's output. The individual values also match: $T_+(1000)=4.6637\times10^{-5}$,
  $Q_+=2.2774\times10^{-2}$, $Q_-=5.5525\times10^{-3}$.
