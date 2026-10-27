# 04. Exposure in experiments that switch at regenerations

Date: 26 October 2026. Research notes for §3 of `F_plan_v2.md`. Nothing here edits the paper.
Scripts in this folder: `04_cycle_law.py` (cycle law, about 1 min) and `04_exposure_law.py` (law of
$A_N$, about 1 min). Both write a `*_output.txt` file, and every check passes. Run them with `py -I`.

**Status in one paragraph.**
- (LR) and (SPAN) for the cycle of a slotted Geo/G/1 queue are proved below. **(LR) is not new**: the
  same local asymptotic is eq. (14) of Kortchemski (AIHP 2015) and Remark 18.34 of Janson (Probab.
  Surveys 2012), read as subcritical Galton–Watson total progeny.
- (LD) for the cycle is proved from F's own Lemma `lem:diff-bigjump`.
- (LD2) is proved modulo one extension of F's Lemma `lem:second-bigjump` (Claim A). The proof of that
  lemma uses its hypothesis $L\ge m\mu$ only in a form that survives $L\ge cm$, but I have not
  re-audited every sub-lemma it calls.
- The five design corollaries hold as stated below, each with an F label behind it. Two of the plan's
  phrasings need correcting:
  - the factor is $N/(s(\alpha-1))$, plus a second atom;
  - the golden-ratio rule is not an "iff" at $\alpha=\varphi$, and it needs equal indices.
- Exact computations agree with every prediction, with relative errors of 1–13% at $N=4000$, all
  shrinking with $N$.
- None of the five switchback papers checked treats heavy-tailed cycles.

---

## 1. The model and the reduction

**Slotted Geo/G/1.**
- In each slot a customer arrives with probability $\lambda$ and brings $\sigma$ slots of work, with
  $\sigma\ge1$ i.i.d.
- So the work arriving in a slot is $W$, with $P(W=0)=1-\lambda$ and $P(W=n)=\lambda f_\sigma(n)$ for
  $n\ge1$. Its mean is $\rho=\lambda E\sigma<1$.
- The workload evolves as $V_t=\max(V_{t-1}-1,0)+W_t$.
- A regeneration is an epoch with $V_t=0$. The cycle $C$ is the number of slots between consecutive
  regenerations, and an idle slot is a cycle of length 1.

**The design.** Each arm sets its own law of $W$; here only $\lambda$ differs, so $\rho_+$ and $\rho_-$
differ. The arm switches at every regeneration. At a switch the system is empty, so the cycles are
independent, and each cycle has the cycle law of its own arm. Hence the number of treated slots among
the first $N$ is exactly F's $A_N$, with $f_\pm$ the cycle law under arm $\pm$.
- A **fresh start** means starting on an empty system.
- A **random-time start** means observing from a typical time of a long-running switchback, which is
  F's stationary initial run $\nu_\sigma=T_\sigma/s$.

`04_exposure_law.py` checks the reduction by simulating 300,000 queues with switching
($N=200$, $\chi^2=18.8$ on 11 df).

**Switching after a geometric number of cycles.** The run is then $R=\sum_{i\le G}C_i$. By
Asmussen–Foss–Korshunov (JTP 2003) Theorem 2(i), with the lattice case in their Remark 3, we get
$f_R(n)\sim E[G]\,f_C(n)$, so (LR) and (SPAN) carry over. (LD) and (LD2) for $R$ are not checked.

## 2. Hypotheses for the cycle (task 1)

Write $f=f_W$ and $T_W(n)=P(W\ge n)$, and assume (LR) for $W$: $f(n)\sim\alpha T_W(n)/n$ with
$T_W\in RV_{-\alpha}$ and $1<\alpha<2$. For Bernoulli arrivals this is (LR) for $\sigma$, since
$f=\lambda f_\sigma$ on $n\ge1$.

**Lemma Q0 (cyclic lemma).** $P(C=n)=P(U_n=n-1)/n$ for $n\ge1$, where $U_n=W_1+\dots+W_n$.

*Proof.*
- Starting empty, $V_1=W_1$, and $V_t=V_{t-1}-1+W_t$ while $V_{t-1}\ge1$. So
  $C=\inf\{t\ge1:U_t-t=-1\}$.
- This is the first passage to $-1$ of the downward skip-free walk $U_t-t$.
- The hitting time theorem (Kemperman; elementary proof by van der Hofstad–Keane, Amer. Math. Monthly
  2008) gives the formula.
- Equivalently, $C$ is the total progeny of a Galton–Watson tree with offspring law $W$ (Dwass 1969).
- Checked against a dynamic program on the workload itself for $n\le300$, with relative difference
  $10^{-15}$.

**Lemma Q1 ((LR) and (SPAN)).**
$$f_C(n)\sim f_W\big((1-\rho)n\big)\sim(1-\rho)^{-\alpha-1}f_W(n),\qquad
T_C(n)\sim(1-\rho)^{-\alpha-1}T_W(n)=E[C]\,T_W\big((1-\rho)n\big)(1+o(1)).$$
So $C$ satisfies (LR) with the same $\alpha$. Since $f_C(1)=1-\lambda>0$ and $f_C(n)>0$ for all large
$n$, it also satisfies (SPAN).

**The exact constant.** For Bernoulli($\lambda$) arrivals with $f_\sigma(n)\sim\alpha c_\sigma n^{-\alpha-1}$,
$$P(C=n)\sim\alpha\lambda c_\sigma(1-\rho)^{-\alpha-1}n^{-\alpha-1},\qquad
P(C\ge n)\sim\lambda c_\sigma(1-\rho)^{-\alpha-1}n^{-\alpha},\qquad\rho=\lambda E\sigma .$$
For the zeta law $f_\sigma(n)=n^{-\alpha-1}/\zeta(\alpha+1)$ this is
$f_C(n)\sim\lambda(1-\rho)^{-\alpha-1}n^{-\alpha-1}/\zeta(\alpha+1)$. The tail form is the
discrete-time analogue of Zwart's and Denisov–Shneer's $P(B>t)\sim E[B]\,P(\sigma>(1-\rho)t)$.

**Proof of Lemma Q1.** It is Kortchemski's route (cyclic lemma plus a local big jump). Here is a
self-contained version using Bennett's inequality. Put $x=n-1$ and $L=x-n\rho=(1-\rho)n-1$, and fix a
small $\delta>0$. Split $P(U_n=x)$ by the number of indices with $W_i>\delta n$.
1. **Two or more.** At most $n^2T_W(\delta n)\sup_{m>\delta n}f(m)\le C_\delta n^2T_W(n)f(n)$, which is
   $o(nf(n))$.
2. **Exactly one.** This is $n\sum_yP(U_{n-1}=y,\max\le\delta n)f(x-y)$.
   - On $|y-(n-1)\rho|\le\varepsilon n$, uniform convergence gives
     $f(x-y)=f(L)(1+O(\omega(\varepsilon))+o(1))$, and this event has probability $1-o(1)$ by the
     weak law.
   - On $y-(n-1)\rho>\varepsilon n$, use $f(x-y)\le C_\delta f(n)$ together with a probability that is
     $o(1)$.
   - On $y-(n-1)\rho<-\varepsilon n$, $f(x-y)\le Cf(L)$ by Potter's bounds, again with probability
     $o(1)$.
   - So this part is $nf(L)(1+o(1))$.
3. **None.** Split $U_n$ into halves; one half exceeds its mean by $L/2$.
   - Bennett's inequality for summands bounded by $\delta n+\rho$, with variance at most
     $E[W^2;W\le\delta n]\le C\delta^2n^2T_W(\delta n)$, gives at most
     $(C\,nT_W(\delta n)/\delta)^{(1-\rho)/(2\delta)}=n^{-(\alpha-1)(1-\rho)/(2\delta)+o(1)}$.
   - This is $o(n^{-\alpha-1})$ once $\delta<(\alpha-1)(1-\rho)/(2(\alpha+1))$.

So $P(U_n=n-1)\sim nf((1-\rho)n)$, which is the claim; the tail follows by Karamata. The constant is
confirmed numerically: the ratio is 0.9996 for $\rho=0.4$ and 0.9972 for $\rho=0.6$ at $n=2^{14}$,
with $\alpha=1.5$ (`04_cycle_law_output.txt`). Convergence is slower for larger $\rho$.

**Lemma Q2 ((LD), sharp form).** If $W$ also satisfies (LD2), then
$f_C(n+1)-f_C(n)=-(\alpha+1+o(1))f_C(n)/n$.

*Proof.*
- Apply F's Lemma `lem:diff-bigjump` (sec_shape.tex) to $W'=W+1$, a law on $\{1,2,\dots\}$ with
  (SPAN), (LR) and (LD2) and mean $\mu'=1+\rho$. With $V_m=f_{W'}^{*m}$,
  $\varphi(n):=nf_C(n)=V_n(2n-1)$, at deviation $L=(1-\rho)n-1\ge Ka(n)$.
- Then $\varphi(n+1)-\varphi(n)=\delta V_n(2n+1)-\nabla V_n(2n+1)-\nabla V_n(2n)$.
- The lemma's asymptotics give
  $f(L)+(\alpha+1)\tfrac{nf(L)}{L}(\mu'-2)+O(\varepsilon)f(L)=(-\alpha+o(1))f(L)$, since
  $\mu'-2=-(1-\rho)$ and $n/L\to1/(1-\rho)$.
- Dividing by $n$ gives the claim.
- Numerically, $n\Delta f_C/f_C$ equals $-2.4987$ at $n=8192$ for $\alpha=1.5$, against $-2.5$.

**Lemma Q3 ((LD2)), modulo Claim A.** $|\Delta^2f_C(n)|=O(f_C(n)/n^2)$.
- **Claim A.** F's Lemma `lem:second-bigjump` (sec_modeproofs.tex) gives
  $|\nabla^2V_m(n)|\le Cmf(L)/L^2$ for $L\ge\max(K_1a(m),L_0,m\mu)$. Its proof uses $L\ge m\mu$ only to
  get $mT(\delta L)\le C_\delta LT(L)$ and $m\le CL$. Both hold under $L\ge cm$, with $c$-dependent
  constants. I believe the bound holds for $L\ge\max(K_1a(m),L_0,cm)$, but I have not re-audited
  `lem:trunc-local`, `lem:truncated` and the cited step of the proof of `lem:diff-bigjump` for any
  other use. Here $L\approx(1-\rho)n<m\mu'=(1+\rho)n$, so the extension is needed.
- **Claim B.** $|\nabla\delta V_m(n)|\le Cf(L)/L$ for $L\ge cm$, proved from A as in F's
  `lem:plus-second`(ii) but with the split at $x=L/2$:
  - write $\nabla\delta V_m(n)=\sum_xf(x)[\nabla V_m(n-x)-\nabla V_m(n)]$;
  - the range $x\le L/2$ gives $\le C\mu'mf(L)/L^2$ by A;
  - the term $-\nabla V_m(n)T(L/2)$ is $o(f(L)/L)$;
  - in the range $x>L/2$, summation by parts moves the difference onto $f$, where (LD) gives
    $Cf(L)/L$, plus a boundary term $\le Cf(L)\cdot mf(L)\le Cf(L)/L$.
- **Claim C.** $|\delta^2V_m(n)|\le Cf(L)/L$:
  - the range $x\le L/2$ is handled by B;
  - the term $\delta V_m(n)T(L/2)$ is $O(f(L)T(L))$;
  - the rest is $E[\gamma(S_m+X)-\gamma(S_m)]$ with $\gamma(y)=f(n-y)\mathbf 1\{n-y>L/2\}$;
  - when both arguments are in range, (LD) gives $\le C\mu'f(L)/L$;
  - when only $S_m$ is in range, the bound is $Cf(L)\cdot P(S_m<n-L/2\le S_m+X)$. That probability is
    $\sum_kT(k)V_m(n-L/2-k)\le C(mf(L)+T(L))\le CT(L)$, which is $\le C/L$.
- **Assembly.** Expand $\Delta^2\varphi(n)$ into $\delta^2V$, $\nabla\delta V$ and $\nabla^2V$ terms at
  $m\in\{n,n+1\}$ and $L\approx(1-\rho)n$. Each is $O(f(L)/L)$. The product rule for differences, with
  $\varphi=O(nf)$ and $\Delta\varphi=O(f)$ (Q2), gives $\Delta^2(\varphi/n)=O(f/n^2)$.
- **Numerics.** $n^2\Delta^2f_C/f_C$ equals 8.7448 at $n=8192$, against $(\alpha+1)(\alpha+2)=8.75$
  ($\alpha=1.5$, $\rho=0.4$). For $\alpha=1.8$ it approaches $10.64$ from above.

**What is new here, and what is not.**
- **Not new:** (LR) for the cycle, via total progeny (Kortchemski eq. (14) under $\mu_n=L(n)n^{-1-\theta}$,
  $\theta>1$; Janson Rem. 18.34 for $w_k\sim ck^{-\beta}$). Denisov–Shneer, "Global and local
  asymptotics for the busy period of an M/G/1 queue" (Queueing Syst. 2010), also exists. I have **not
  read it**, and it may contain the continuous-time local busy-period result. Read it before claiming
  anything about M/G/1.
- **Not found stated elsewhere (limited search):** (LD) and (LD2) for the cycle.

**Other versions (not proved here).**
- **Poisson batch arrivals per slot.** $W$ is compound Poisson, and $f_W\sim\lambda f_\sigma$ by AFK
  Theorem 2(i), so Q1 applies. Q2 and Q3 would need (LD2) for compound Poisson.
- **Embedded M/G/1, counting customers.** The number served in a busy period is total progeny with
  offspring $A=\mathrm{Pois}(\lambda\sigma)$. Q1 applies once $f_A$ satisfies (LR), for instance if
  $\sigma$ has a regularly varying density $g$, with then $f_A(n)\sim g(n/\lambda)/\lambda$. I have not
  written out this Laplace-method step.

**(EQ).** Both arms use the same service law, so $T_\pm(n)\sim c_\pm n^{-\alpha}L(n)$ with the same
$L$, and (EQ) holds. If treatment changed the service tail index, (EQ) would fail and the mode count
would not apply (F `rem:mode-open`).

## 3. Corollaries in design language (task 2)

**Notation.**
- $f_\pm$ is the cycle law under treatment/control, $T_\pm(n)=P(C_\pm\ge n)$, and
  $\mu_\pm=1/(1-\rho_\pm)$.
- $s=\mu_++\mu_-$, and $p=\mu_+/s$ is the long-run treated share.
- $B_N$ is the stable scale (F eq. `eq:scales`), regularly varying with index $1/\alpha$.

**Hypotheses.** All are verified for the slotted Geo/G/1 with locally regularly varying service by §2,
and (LD2) is conditional on Claim A.

**E1. Exposure imbalance at scale $N^{1/\alpha}$.** Assume (RV) and (SPAN) for a fresh start.
- *Statement.* $\sup_k|B_NP(A_N=k)-h_N((k-pN)/B_N)|\to0$, and $P(A_N=k)\le C/B_N$ for every $k$.
- Hence $(A_N-pN)/B_N\Rightarrow W_\theta$ along subsequences on which $\theta_N$ converges, with
  $W_\theta=(1-p)\theta_+Z_+-p\theta_-Z_-$ a skewed stable law.
- The treated-share error $A_N/N-p$ is therefore of exact order $N^{1/\alpha-1}$. It is not
  $N^{-1/2}$ and not Gaussian.
- The no-switch atoms do not change this, by `thm:preparation`(b).
- *Behind it:* `thm:bulk`(a),(b), and for a random-time start `thm:preparation`(b) with
  `cor:stationary`, since the bulk criterion holds.
- *Remarks.*
  - The distributional limit alone is classical (Takács 1957 for sojourn times). What F adds is the
    local, uniform-in-$k$ form, including the bound $C/B_N$ at every point.
  - In design terms there is also a deterministic imbalance $(2p-1)N$ whenever $\rho_+\ne\rho_-$, since
    the treated cycles are longer. The random part is of order $N^{1/\alpha}$.
- *Numerics* ($\alpha=1.5$, $\rho_\pm=0.6/0.4$): $B_NP_N(pN)$ is 0.341, 0.328 and 0.318 at
  $N=1000$, 2000 and 4000, against $h(0)=0.282$. Convergence is slow but monotone.

**E2. Severe imbalance (one arm gets fewer than $\varepsilon N$ periods).** Assume (RV) and (SPAN) for
both arms and (LR) for treatment, a fresh start of either arm, and fixed $\varepsilon\in(0,1-p)$. Put
$\ell_\varepsilon=1-\varepsilon/(1-p)$. Then
$$P(N-A_N<\varepsilon N)\sim N\,T_+(N)\,\frac{\varepsilon}{\mu_-}\,\ell_\varepsilon^{-\alpha_+}.$$
- *Behind it:* the additive form of `thm:bigjump`(b) on $[(1-\varepsilon)N,N]$, which lies in the
  zone for large $N$ because $\lambda_NB_N=o(N)$.
- *Proof.*
  - $G_N(\lfloor vN\rfloor)/T_+(N)\to I_+(v)$ uniformly on compacts of $(p,1)$, by the computation in
    `cor:infinite-density` and uniform convergence (`lem:rv`(i)).
  - The last $\delta N$ points contribute $\le C\delta NT_+(N)$, by `thm:bigjump`(c).
  - Then $\int_{1-\varepsilon}^1I_+=\varepsilon\ell_\varepsilon^{-\alpha}/\mu_-$, because
    $\alpha(1-\ell)\ell^{-\alpha-1}+\ell^{-\alpha}=-\frac{d}{d\ell}[(1-\ell)\ell^{-\alpha}]$.
  - The atom $T_+(N)$ is of lower order.
- *Random-time start.* By `cor:stationary`(a),(b) one term is added, which is the complete initial
  cycle:
  $$P(N-A_N<\varepsilon N)\sim NT_+(N)\Big[\frac{\varepsilon}{\mu_-}\ell_\varepsilon^{-\alpha}+\frac{\ell_\varepsilon^{1-\alpha}}{s(\alpha-1)}\Big].$$
  As $\varepsilon\to0$ the fresh value vanishes linearly while this one does not.
- The mirror statement (treatment gets fewer than $\varepsilon N$) holds with signs exchanged. Its
  zone uses $\lambda_N=1+\log(1/\theta_{-,N})$, still $o(N)$.
- *Numerics* at $N=4000$:
  - exact/predicted is 1.076, 1.063 and 1.066 (fresh) and 1.009, 1.012 and 1.022 (random) for
    $\varepsilon=0.05$, 0.1 and 0.2;
  - the ratios were 1.15, 1.12 and 1.09 at $N=1000$;
  - the mirror ratio is 1.13.

**E3. No switch at all.** The event $\{A_N\in\{0,N\}\}$ is exactly "the first cycle covers all $N$
slots".
- For a fresh start in treatment, $P=T_+(N)$ exactly (`prop:fresh-identity`).
- For a random-time start, $P=Q_+(N)+Q_-(N)$ exactly (`prop:first-run`). Here
  $Q_\sigma(N)=s^{-1}\sum_{d\ge N}T_\sigma(d)\sim NT_\sigma(N)/(s(\alpha-1))$ (`cor:stationary`(a)).
- These are exact identities with no hypothesis, plus (RV) for the asymptotic.

**E4. Where to start: the factor.**
$$\frac{P_{\rm random}(\text{no switch})}{P_{\rm fresh+}(\text{no switch})}\sim\frac{N}{s(\alpha-1)}\Big(1+\frac{T_-(N)}{T_+(N)}\Big).$$
- The plan's "factor of order $N/(\alpha-1)$" is right in order. The exact same-arm factor is
  $N/(s(\alpha-1))$, and the random start adds the second arm's atom.
- The random start also adds the complete initial cycle to the big-jump kernel (`cor:stationary`(b)),
  and so to E2.
- *Design rule:* start the experiment at a regeneration (an empty system).
- *Numerics:* the exact ratio is 607, 1204 and 2396 against the asymptotic 599, 1195 and 2387 at
  $N=1000$, 2000 and 4000.

**E5. The golden-ratio rule.** Assume (RV) and (SPAN), equal indices $\alpha_+=\alpha_-=\alpha$, and a
random-time start. Then:
- for $\alpha<\varphi$ the single most likely value of $A_N$ is an endpoint (0 or $N$, that is, no
  switch) for all large $N$;
- for $\alpha>\varphi$ it is interior for all large $N$ (`thm:mode`(d)).

*Corrections to the plan's wording.*
1. It is not an "iff" at $\alpha=\varphi$. On that line the comparison depends on slowly varying
   factors. For pure power tails F gives interior, with $\mathcal C(\varphi)=0.776$; for these queue
   cycles the constant is not computed.
2. "No switch" is two outcomes. The theorem compares each endpoint atom with the largest interior
   value, not their sum.
3. It holds for all large $N$, not for every $N$.
4. With unequal indices the criterion is per arm: $\alpha_\sigma-1<1/\alpha_*$.

*Extension, from `thm:mode`(c).* The same threshold holds if the experiment starts at a typical time of
a system that ran in control only, with the cycle in progress kept in control
($\nu_-=T_-/\mu_-$, $Q_-\in RV_{-(\alpha-1)}$, bulk criterion holds).

For a fresh start the mode is always interior (`thm:mode`(d), last sentence).

*Numerics:* $\max$ atom / $\max$ interior is
- 3.28, 3.81 and 4.39 for $\alpha=1.5$ (random start);
- 1.92, 2.24 and 2.60 for $\alpha=1.5$ (control-only start);
- 0.291, 0.253 and 0.220 for $\alpha=1.8$ (random start);
- 0.151, 0.133 and 0.116 for $\alpha=1.8$ (control-only start);

at $N=1000$, 2000 and 4000. The trends match $N^{1-\alpha+1/\alpha}$.

**E6. Three modes (bonus).**
- *Behind it:* `thm:mode-count` and `cor:logconvex-three`, under (SPAN), (LR), (LD2) and (EQ), with a
  fresh start.
- *Result:* the exposure law has exactly three modes for all large $N$ (no switch to either side, and
  the bulk), provided each end profile has one local maximum.
- *Status.*
  - This holds if $f_\pm$ is strictly log-convex. That is checked only numerically ($n<2^{14}$; the
    margin at the top is about 40 times the estimated float error).
  - It is not proved for total-progeny laws.
  - (LD2) rests on Claim A.
- *Numerics:* exactly 3 modes at $N=1000$, 2000 and 4000, and $u_-$ is decreasing on $j<60$.

## 4. Positioning (task 4)

All sources were verified from arXiv text. Each line gives what the paper assumes about time
dependence.
- **Bojinov, Simchi-Levi, Zhao**, *Design and analysis of switchback experiments*, Manag. Sci. 69 (2023),
  arXiv 2009.00148. Assumption 2, $m$-carryover: outcomes depend only on the last $m+1$ assignments,
  with $m$ fixed and known.
- **Hu, Wager**, *Switchback experiments under geometric mixing*, arXiv 2209.00197. Assumption 2: a
  Markov state with geometric total-variation mixing, $e^{-1/t_{\rm mix}}$ contraction; the carryover
  decays exponentially.
- **Glynn, Johari, Rasouli**, *Adaptive experimental design with temporal interference: a maximum
  likelihood approach*, NeurIPS 2020, arXiv 2006.05591. Irreducible Markov chains on a finite state
  space. §7 mentions regenerative policies that switch only at visits to a fixed state. Finite state
  means light-tailed cycles.
- **Li, Johari, Kuang, Wager**, *Experimenting under stochastic congestion*, arXiv 2302.12093. A
  birth–death queue with exponential service and a bounded queue (Assumption 1, $K<\infty$). It
  analyses interval switchbacks and **regenerative switchbacks** that re-randomize at hits of a state
  (App. A.3.1). Cycles are light-tailed.
- **Jia, Kallus, Yu**, *Clustered switchback designs for experimentation under spatio-temporal
  interference*, arXiv 2312.15574. Assumption 4, rapid (geometric) mixing per unit, plus neighbourhood
  spatial interference.
- **Hu**, *Spectral design of random-duration switchbacks*, arXiv 2609.13698. The assignment is an
  alternating renewal process with a designed run law of finite mean, under finite carryover $m$. It
  does not treat heavy-tailed runs.

**Gap.** Every design above assumes geometric mixing, finite carryover, or a finite or bounded state,
so regeneration cycles are light-tailed. None treats exposure when the cycles have infinite variance.
In that regime, by E1–E5:
- the exposure count is non-Gaussian at scale $N^{1/\alpha}$;
- its extremes are given by a big-jump kernel;
- the start matters by a factor of order $N$;
- the mode can sit at "no switch".

This rests on searching, not proof. Also relevant and verified: Starreveld–Bekker–Mandjes
(arXiv 1602.05131) is the light-tailed occupation-time counterpart (transform, CLT under finite
variances, LDP under exponential moments).

## 5. Open items

1. Write out Claim A, or re-audit `lem:second-bigjump`'s dependencies, to close (LD2) for the cycle.
2. Read Denisov–Shneer (Queueing Syst. 2010) before stating anything about M/G/1 busy periods in
   continuous time.
3. Log-convexity, or monotone $u$, for total-progeny laws, to make E6 unconditional.
4. Check Doney (1989) itself; only the first page was reachable. Q1 does not depend on it.
