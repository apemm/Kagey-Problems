# Referee report

**Manuscript:** "Bulk, big jumps and boundary layers in the occupation law of a lattice Lévy walk"
**Journal:** Electronic Journal of Probability
**Files read:** `problem131_levy.tex` (front matter, abstract, bibliography), `sec_intro.tex`, `sec_setting.tex`, `sec_bulk.tex`, `sec_bigjump.tex`, `sec_preparation.tex`, `sec_shape.tex`, `sec_inverse.tex`. As instructed, `sec_verify.tex` is a placeholder and I did not review it.

**Recommendation: major revision.**

## Summary of the submission

The paper studies $P_N(k)=\mathbb P(A_N=k)$, where $A_N$ is the number of plus slots among the first $N$ in an alternating sequence of independent runs. The run lengths have regularly varying tails of index $\alpha_\pm\in(1,2)$, and the first run (the "preparation") is arbitrary. The main results are:

- **Theorem A (bulk).** A uniform local limit theorem over the whole row, with a moving stable profile $h_N$ and the bound $\sup_k P_N(k)\le C/B_N$. It holds under (RV) and (SPAN), for every relation between the two scales.
- **Theorem B (big jumps and the boundary layer).** One kernel $G_N=\gamma(N-k)f_+(\lfloor L_k\rfloor)+T_+(\lfloor L_k\rfloor)\kappa(N-k)$ describes $P_N(k)$ with relative error $o(1)$ on the zone $pN+K\lambda_NB_N\le k\le N$, in the double limit, under (LR). The paper adds a fixed-$j$ boundary layer under (RV) alone, a uniform layer, a one-sided lower bound on the larger zone $pN+KB_N\le k\le N$, and the infinite density.
- **Theorem C (preparation).** Exact first-run corrections in each zone, with if-and-only-if criteria. It covers the stationary start and shows that no $o(N)$ trim works for every preparation.
- **Theorems D and E (shape).** The global mode is decided by comparing the endpoint atom with $H_N/B_N$ (the golden-ratio threshold for the stationary start, with the constant $\mathcal C(\varphi)$). The antimode sits at $T_-(j^*_N)\sim 2\alpha_+s/N$, using an exact second-order boundary-layer coefficient $C(j)$.
- **Theorem F (identification).** The run laws are recovered from the two ends.

I checked every theorem against its proof and every proof against the lemmas it cites. I found **no error that invalidates a main theorem.** Within the scope I checked, the mathematics is careful, and several delicate points are handled correctly:

- uniformity in the ratio of the scales in Theorem A;
- the exact coefficient $\gamma$ at bounded $j$ where $\kappa(j)=0$;
- the left-deviation mechanism behind $\lambda_N$;
- the use of the one-sided bound in the antimode proof.

I recommend major rather than minor revision for four reasons:

1. Several claims in the abstract and introduction say more than is proved. The main ones are the necessity of (LR), "no single formula", and a description "over the whole row" that has a gap when $\theta_{+,N}\to0$.
2. The positioning against Rebenshtok, Denisov, Hänggi and Barkai is inaccurate on a point the paper makes central.
3. The manuscript is much longer than its new content needs. A large share of the 62 pages is classical material re-proved or the same fact proved two or three times.
4. Several numerical statements in the body rest on a verification section that does not yet exist.

---

## 1. Correctness

### 1.1 Section 2 (setting and exact identities)

- **Exact identities.** I checked Proposition 2.2 (fresh-plus identity), Proposition 2.3 (first-run decomposition), Lemma 2.4 (Green identity), Proposition 2.5 (final-run identity and recursion) and Lemma 2.6 (counting) line by line. All are correct, including the endpoint cases. Two examples of what I checked:
  - The plus case with $i=1$ vanishes because $u^-_0(l)=0$ for $l\ge1$.
  - For $j=0$, only $t=0$ contributes to the final-run identity.
- **Kernel (2.4).** $\kappa^{(+)}_+=u_-$ and $\kappa^{(-)}_+=u_-\mathbf 1_{j\ge1}$ are correct.
- **Lemma 2.1 (profile).** Correct. The positivity argument for $g_\sigma$ (Step 4) is a valid self-contained proof of a classical fact. See §5 for length.
- **Hypothesis (LR), sec_setting.tex:56–58, 65.** (LR) is stated with the $\alpha_\sigma$ of (RV), so as written it presupposes (RV). The text then says that (LR) implies (RV) "by Karamata's theorem". The implication is true: $T(n+1)/T(n)=1-\alpha/n+o(1/n)$, and the representation theorem gives $T\in\mathrm{RV}_{-\alpha}$. But the representation theorem is the right citation, not Karamata's theorem. State (LR) with its own index, or say that it is assumed in addition to (RV).

### 1.2 Section 3 (bulk)

I checked the following. All are correct.

- Lemma 3.2 (i): the normalization $F(1)=\Gamma(2-\alpha)/(\alpha-1)=-\Gamma(1-\alpha)$ and the sign convention $K_\alpha(-i\theta)^\alpha$.
- Lemma 3.2 (iv), and Lemma 3.4 including its constants.
- The index computation in Lemma 3.4: the sum of the exponents is at most $1-\alpha_*<0$.
- Lemma 3.5 (a): the handling of $J-1\notin I$ for the kernel $q_{m+1}$.
- Lemma 3.6, and both forms of the profile formula: I verified the substitution and the Jacobian $s/(\theta_+\theta_-)$.
- Step 4: the choice $K=\mu_{\min}R/(2\mu_{\max})$ and the resulting lower bound $sRB_N/(2\mu_{\bar\tau})$.
- Step 5: the weights in (3.11) sum to $s$, and the Riemann-sum argument at the level $k_{\bar\tau}$ applies uniformly over $\Psi(\omega)$.

The proof is uniform in $\theta_N$ as claimed. Step 6 is a remark, not a step.

One point needs checking. Lemma 3.2 (iii) depends on [Caravenna–Doney 2019, Theorem 1.1, (1.6)] holding for $\alpha\in(1,2)$, with mean zero, without aperiodicity, for **all** $x\ge0$ and $m\ge1$. Please quote the hypotheses of (1.6) exactly. In particular, say whether that bound is stated for $\alpha\in(1,2)$ or only for $\alpha<1$ with the case $\alpha>1$ handled separately. Lemma 3.4 and Step 2 of the bulk proof stand on it.

### 1.3 Section 4 (big jumps)

**Theorem 4.1 (a).** Correct, and it does use only (RV) for the plus sign:

- (RV) alone gives $f_+(n)=o(T_+(n))$, because $T(n+1)/T(n)\to1$.
- The tail of $\rho_j$ beyond $N/4$ is controlled by (4.10), which needs no local hypothesis.
- (SPAN) is not used.

**Lemma 4.3 (truncated deviations).** Correct. I checked $\vartheta^2e^{-\vartheta}\le1$.

**Lemma 4.4 (no giant run).** Correct for the plus start.
- I checked the exponent $r=z/(2w)=1/(16\eta)$.
- I checked that the supremum over $m\le M$ is attained up to a constant at $m=M$, because $m^r/a_+(m)$ is regularly varying with a positive index.
- The minus start is dismissed in one sentence (sec_bigjump.tex:346–348). Please write the index shifts out, at least in a footnote.
- Line 366 says the two halves satisfy $|I_h|\ge m/3$, but the bound then uses $a_+(\lfloor m/2\rfloor)$. Take the halves of sizes $\lfloor m/2\rfloor$ and $\lceil m/2\rceil$.

**Lemmas 4.5–4.7.** Correct. I checked:
- the pair-counting masses $(1+\mu_+)(j+1)^2$ and $j+1$;
- the bound $(1+R)\mathbf 1_{|S-c_i|>z/2}+R\mathbf 1_{R>z/2}$ in Lemma 4.6;
- the mass bound $(2+\mu_+)j\varepsilon$ for the far $z$ in Lemma 4.7;
- the choice $Z/K\le\eta/2$, which makes the indicator in $C_\lambda$ equal to one.

**Proof of (b), (c).** Correct. I checked:
- that the small-$j$ case kills the no-giant term through Lemma 2.6 once $\eta\le1/(2J_0+2)$;
- the lower bound $G_N\ge c_6(N/L)T_+(L)$;
- the three ratio bounds, including the $\varrho>1$ case, which is exactly where $\lambda_N=1+\log\varrho$ is needed.

The additive form with the limit coefficient $(N-L_k)/\mu_-$ follows as stated.

**Corollary 4.8 (lower bound).** Correct on the larger zone $pN+KB_N\le k\le N$. No step uses $\lambda_N$.

**Corollary 4.9 and Remark 4.10.** Both computations are correct. I recomputed the ratios $h(K)/(\alpha_+(1-p)^{\alpha_+}K^{-\alpha_+-1})=0.3126,\ 1.6774,\ 1.0934$ at $K=1,4,16$ for $\alpha=3/2$, and they match the text.

**Example 4.12.** The verification is correct: the spike at $n_i$ enters $G$ at full weight, while $\sup_z\nu_j(z)=o(j)$. But the conclusion drawn from it is stronger than what it proves. See §2.

### 1.4 Section 5 (preparation)

**(a), (b), (d).** Correct. The disjoint supports of the two defects and the bound $\Delta_{+,N}\ge B_N\nu_+(N-1)$ give the if-and-only-if criteria cleanly.

**Proof of (c).** Correct.
- I checked the geometry in Step 1:
  - $L^{(n)}_k=L+pd/(1-p)$ for $d\le j$;
  - $L^{(n)}_{k-d}=L-d$ for $d<L/2$;
  - the use of $\lambda_n\le2\lambda_N$ for $n\in[cN,N]$.
- I checked that the $S_1+S_3$ weights reassemble exactly into $G^\nu_N$ with the prepared kernel (5.2). The $\pi_\plus$ term of $G^\nu$ double-counts the first plus runs with $d\ge L_k/2$, but this is absorbed into $\mathbb P(D>J)\widehat G_N$, which is fine.

**Window criterion.** The necessity argument (via Theorem A (c)) and the sufficiency argument (the block decomposition, under (LR) for both signs) are correct. I checked the four block sums.

**Corollary 5.9 (stationary).** Correct: $\kappa_+=pu_-+1/s$, $\kappa^{\rm st}_+=(2/s)(1+\mu_+u_-)$, and the limit $2/\mu_-$ at $v=1$.

**Corollary 5.10 (no trim).** Correct.

**One forward reference.** At sec_preparation.tex:110–111 the bound $\nu_+(d)K^-_{N-d}(j)\le C_j\nu_+(d)T_+(N)$ is attributed to Theorem 4.1 (a). Theorem 4.1 (a) is a limit statement. The uniform bound is Lemma 7.2 (end-crude) of Section 7, which should be cited, or the lemma should be moved to Section 2.

### 1.5 Section 6 (shape)

**Theorem 6.1.** Correct. I recomputed $\mathcal C(\varphi)=0.77613172\ldots$ and the elementary upper bound $0.95136\ldots$. The trapezoid bound $\zeta(\varphi)\ge\varphi+\tfrac12$ is valid. Part (d) is a comparison of exponents ($\alpha-1$ against $1/\alpha$) plus one constant.

**Theorem 6.3 and Proposition 6.6.** Correct. I checked:
- the expansion $1+\alpha(j+2r\mu)/N$ for the censored run;
- the identities (6.6)–(6.8);
- the limit $C(j)/j\to2\alpha_+s/\mu_-^2$.

The coefficient agrees with the big-jump kernel at the junction. Expanding $\gamma(j)f_+(N)+T_+(N-js/\mu_-)u_-(j)$ gives $u_-(j)+2\alpha_+sj/(\mu_-^2N)$ to first order. This is a useful consistency check, and the paper might state it.

**Lemma 6.4 (uniform local big jump).** Correct. I checked the exponential Chebyshev step and the choice $\Lambda=xy/(qb)$.

**Theorem 6.8 (antimode).** Correct.
- Step 1 uses Proposition 6.6 on $j\le K\Lambda_N\le N^{1-\eta}$.
- Step 2 uses Potter's lower bound for $jT_-(j)$.
- Step 4 uses Corollary 4.8, the lower bound on the larger zone, together with Theorem A (c) on $|k-pN|\le KB_N$. This is exactly the right combination: no upper bound in the $\lambda_N$ window is needed.

**Lemma 6.7 (log-convexity).** Correct, given de Bruijn and Erdős.

### 1.6 Section 7 (identification)

- **Theorem 7.1 (a).** Correct. It is immediate from Theorem 4.1 (a) plus the renewal inversion.
- **Theorem 7.1 (b).** Correct, but its proof repeats the proof of Theorem 5.1 (d). Moreover, its hypothesis $L^+_N(j)/(B_NT_+(N))\to0$ is equivalent to $\nu_+(n)=o(T_+(n))$ by the argument at sec_preparation.tex:419–426. So (b) is Theorem 5.1 (d) plus the inversion. State it that way, with that hypothesis.
- **Remark 7.3 (thinning).** Correct. $1/(1-F_c)=1+c(U-1)$ holds, and the tail $T_+(n)/c$ follows from geometric sums of subexponential variables. Cite the precise statement in Embrechts, Klüppelberg and Mikosch, for example their Lemma A3.20 or Theorem A3.20 (check the numbering).
- **Remark 7.4, last sentence (sec_inverse.tex:191–196).** It asserts an identification result "by a fixed-point argument … that we leave to separate work". This is an unproved claim. Remove it or label it as a conjecture.

### 1.7 Interplay between sections (specific checks requested)

**Zone $pN+K\lambda_NB_N$.**
- Theorem 4.1 (b) is stated and proved on this zone.
- Lemma 5.5 (ii) restates it at a general horizon $n$ with $\lambda_n$.
- The proof of Theorem 5.1 (c) moves from $\lambda_N$ to $\lambda_n$ correctly, via (5.6) and $K\ge4K_0$, for both the $d\le j$ shifts and the $d<L/2$ shifts.
- The window-sufficiency proof deliberately avoids the zone and uses (5.11) instead. This is legitimate, and the paper says why at sec_preparation.tex:586–588.

**One-sided lower bound.**
- Corollary 4.8 is used once, in (6.18), on the zone $pN+KB_N\le k\le N$ without $\lambda_N$, exactly as stated.
- In Section 6 nothing uses an upper bound in the window $KB_N\le k-pN\le K\lambda_NB_N$. Good.

**Additive form with the size function.**
- Theorem 5.1 (c) needs the additive form with the limit coefficient $(N-L)/\mu_-$ and size function $\widehat G_n$. This is the last clause of Theorem 4.1 (b), as Lemma 5.5 (ii) says.
- The same function appears under two macros, $\hat G_N$ (sec_bigjump.tex:66) and $\widehat G_N$ (sec_preparation.tex:33). Unify them.

**Exact coefficient $\gamma$.**
- The ratio forms (Theorem 4.1 (b), (c)) use the exact $\gamma$.
- Every later use is additive (Theorem 5.1 (c)), or is in a regime where the censored term dominates at bounded $j$:
  - Corollary 5.9 (b), where $\kappa^{\rm st}\ge2/s$;
  - Remark 4.10 and (6.18), which use only the censored term.
- So nothing downstream needs the ratio form with the limit coefficient. This is consistent.

**Prepared kernel $\kappa_+$.**
- (5.2) and Theorem 7.1 (b) define the same function for $j\ge1$.
- At $j=0$ the prepared kernel is $0$, while the fresh kernel has $\kappa^{(+)}_+(0)=1$. This is consistent, because the atom $Q_+(N)$ is carried separately.
- The introduction, however, writes $\kappa_+$ for the *fresh* kernel (sec_intro.tex:88–92, "$\kappa_+=u_-$ for a plus start"). With $\kappa_+(0)=0$ the displayed formula would give the wrong value at $k=N$. Use $\kappa^{(+)}_+$ in the introduction, or rename the prepared kernel.

---

## 2. Do the abstract and introduction claim exactly what is proved?

**(a) "the big-jump theorem needs the local form of regular variation, which we show is necessary" (abstract, problem131_levy.tex:61–62); "(RV) alone does not control a single bin in the big-jump zone" (sec_intro.tex:101–102).**

Both overstate what Example 4.12 shows. The example shows that $P_N(k)/G_N(k)\to0$ for the particular kernel $G_N$, which reads $f_+$ at one point. The text after the example (sec_bigjump.tex:861–864) says that $P_N$ sees $f_+$ averaged over a window of width $B_N$. That points to an (RV)-only formula with a window average, so (RV) may well control the bin. Remark 4.13 then says that (LR) is *not* necessary on the ballistic range, since window regularity plus $f_+=O(T_+/n)$ suffices.

What is proved is narrower: some local regularity beyond (RV) is needed for the pointwise kernel $G_N$. Rephrase the abstract and introduction to say exactly that.

**(b) "no single formula approximates the law uniformly" (abstract, problem131_levy.tex:52–53); "no single formula approximates $P_N$ with relative error $o(1)$ over the whole row" (sec_intro.tex:99–101).**

Remark 4.11 shows this only for $h_N/B_N$, $G_N$ and their sum. "No single formula" is not a mathematical statement, since a piecewise expression or $P_N$ itself is a formula. Say "neither the bulk profile nor the big-jump kernel nor their sum".

**(c) "We describe $P_N$ bin by bin over the whole row" (sec_intro.tex:15–16; also the abstract, line 46–47).**

When $\theta_{+,N}\to0$ (for instance $\alpha_+>\alpha_-$) there is an undescribed window $KB_N\le k-pN\le K\lambda_NB_N$. There the paper proves only:
- the additive bound $|B_NP_N-h_N|=o(1)$, which says nothing relative once $P_N\ll1/B_N$; and
- the lower bound $P_N\ge(1-\varepsilon)G_N$.

Remark 4.11 even says that the factor in front of $B_N$ must tend to infinity and that the sharp factor is unknown. The introduction says "Every statement below holds for every relation between the two scales" (line 68–69). That is true of each statement, but it suggests a complete picture, which this case does not have. State the gap in the introduction. A natural conjecture is that $P_N\approx h_N/B_N+G_N$ on that window.

**(d) "The pieces join continuously" (abstract).**

- The layer-to-zone junction is a genuine continuity statement: $\kappa(j)\to1/\mu_-$, and one kernel covers both pieces.
- The bulk-to-zone junction holds only in the double limit, through the matching of $h_N$'s tail with the leading term of $G_N$.
- When $\theta_{+,N}\to0$ the bulk-to-zone junction is not established; see (c).

Qualify the sentence.

**(e) "The first run enters each piece through a sharp criterion, and we give the correction when a criterion fails" (abstract).**

- In the interior of the big-jump zone the criterion is sharp only under (LR) for **both** signs. Otherwise the paper has a sufficient condition ($\nu_+=o(T_+)$) and a different necessary one ($W_n=o(T_+)$).
- The big-jump correction $\Psi_N$ is the exact contribution, but it is defined through the fresh law itself, so "we give the correction" is close to tautological except under (R$\nu$).

Say both things.

**(f) Introduction, sec_intro.tex:113–117.** The text reads: "invisible in the big-jump zone exactly when $\nu_+(n)=o(T_+(n))$, and at the plus end only when in addition the first minus run has the fresh law. The three conditions are nested." It mixes two different statements.

- With $\nu_+=o(T_+)$, the big-jump zone of Theorem 5.1 (c) extends to $k=N$. There $P_N\approx G^\nu_N$, and $G^\nu_N$ still depends on $\nu_-$ through $\kappa_+(N-k)$ at bounded $N-k$. So "invisible in the big-jump zone" holds only away from the end.
- The nested chain the theorem states (sec_preparation.tex:96–99) is $Q_+=o(T_+)\Rightarrow\nu_+=o(T_+)\Rightarrow B_n\nu_+(n)\to0$. It involves the atom, not the law of the first minus run, and it nests only the plus halves of the conditions.

Rewrite the paragraph so that it matches the theorem.

**(g) Antimode in the abstract and introduction.**

- The abstract says the interior minimum "sits at the stable scale of the opposite runs". That is proved only for a fresh start and only under $u_->1/\mu_-$. Under the opposite hypothesis the minimum is at bounded distance (Theorem 6.8 (b)).
- The introduction mentions the condition but not the fresh start.

**(h) sec_intro.tex:96–97.** "$P_N(N-j)\sim T_+(N)\kappa_+(j)$, which needs only (RV)." Theorem 4.1 (a) is the statement $P_N(N-j)/T_+(N)\to\kappa(j)$. That is not an asymptotic equivalence when $\kappa(j)=0$, which the paper itself says can happen.

### Positioning

**Rebenshtok, Denisov, Hänggi and Barkai.** The introduction says they "set aside the contribution of a run that is still going at the observation time" (sec_intro.tex:158–160). After Corollary 4.9 the paper says its result includes "the censored-run term" (sec_bigjump.tex:729–732). Both statements are inaccurate as written.

Their PRL (arXiv:1312.3831, Eq. (8) and Eq. (10)) gives, for the two-state *velocity* model,
$$|v/v_0|^{-1-\alpha}\bigl[\alpha-(\alpha-1)|v/v_0|\bigr].$$
The paper's $I_+$ has exactly this shape:
$$\alpha(1-\ell)\ell^{-\alpha-1}+\ell^{-\alpha}=\ell^{-\alpha-1}\bigl[\alpha-(\alpha-1)\ell\bigr].$$
The $-(\alpha-1)\ell$ term is precisely the combination of the complete-run term with the censored-run term. RDHB contrast this with the *jump* model, which gives $[1-|v/v_0|]$ and has no censored contribution. So the censored run is in their velocity-model formula; what they lack is a proof.

I could not find a call for a rigorous treatment in the PRL. If it is in the PRE, quote it. The fair and still strong positioning is that Corollary 4.9 is a rigorous lattice version, for alternating directions, of their formula, together with:
- uniformity up to the end;
- the exact kernel at bounded $j$;
- the matching with the bulk as a theorem rather than the formal matching of their Eqs. (16)–(17).

Also note that the physics Lévy walk chooses each direction independently, while here directions alternate. With independent symmetric directions, consecutive same-sign flights merge, giving the alternating model with geometrically thinned run laws ($c=1/2$ in Remark 7.3). One sentence saying so would connect the two models and use the paper's own remark.

**Vezzani, Barkai and Burioni.** The claim that they "write [the censored term] as a separate contribution and … leave [its derivation] open" (sec_bigjump.tex:731–732) should be supported by a precise quotation or equation number.

**Wang, Schulz, Deng and Barkai.** Likewise, the claim that they "leave the effect of the preparation on the rare fluctuations to future work" (sec_intro.tex:166) needs a quotation, since "Theorem 5.1 answers that question" rests on it.

**Golden ratio (Wang, Li and Hänggi; Cipriani, Denisov and Politi; Lee-Dadswell, Nickel and Gray).** "Theorem 6.1 is the lattice form of their observation with its constant" is fair. The paper should say plainly that the threshold itself is the exponent identity $\alpha-1=1/\alpha$, and that what is new is the theorem-level comparison and the constant $\mathcal C(\varphi)$.

**Berger.** The paper concedes that Berger's Theorem 3.3 with Proposition 2.2 gives the window $|k-pN|\le KB_N$ "for every relation between the two scales". Please check that Berger's multivariate setting allows marginals with *different* indices and a normalization with oscillating ratios. If it does, Theorem A's new content reduces to:
- the uniform $C/B_N$ bound, which is a short consequence of Gnedenko's theorem and (K1); and
- the remote bins.

Either way, that should be reflected in the length of Section 3.

**Melbourne, Pène and Terhesiu.** The arXiv number 2610.15720 is very recent. Check the theorem number and the description "first and last run restricted to fixed lengths" against the final version. "Theorem A removes the restrictions" should say "in the i.i.d. renewal setting", since their result covers a much wider class of dynamical systems.

**Caravenna and Doney; Denisov, Dieker and Shneer; Berger, Birkner and Yuan.** Fair. See §1.2 for the exact hypotheses of (1.6).

---

## 3. Hypotheses

I traced each use.

**(SPAN).** It enters only through Lemma 3.2 (ii) and the renewal theorem (Lemma 3.5, and $\kappa_*$, $\gamma_*$ in Lemma 4.7). It is listed as a hypothesis in several places where it is not used:

| Statement | Hypotheses actually used |
|---|---|
| Theorem 4.1 (a) | (RV) for plus only; the text says so at line 86–87 |
| Theorem 5.1 (d) | (RV) only, and (R$\nu$) for the last clause; sec_preparation.tex:114 says "(RV) and (SPAN)" |
| Theorem 7.1 (a) | (RV) for both signs; (SPAN) is not needed |
| Proposition 6.6 | correctly states only (RV) and (LR) for plus |

Consider stating the minimal hypotheses in these places. It strengthens the identification theorem, and it makes Remark 7.3's check of (SPAN) unnecessary.

**(LR).** It is used only where stated: Theorem 4.1 (b), (c); Lemma 4.5; the $I_\lambda$ part of Lemma 4.7; Corollaries 4.8 and 4.9; Theorem 5.1 (c); Corollary 5.9 (b); Lemma 5.5; Theorem 6.3; Lemma 6.4; Proposition 6.6; Theorem 6.8. I found no hidden use.

**(RV) for the minus sign in Theorem 4.1 (b).** It is used only in the second term of Lemma 4.4 and in Lemma 4.6. That is consistent with "for both signs".

**The "needs only (RV)" claims.** I checked each:
- Lemma 3.2 (i), (iii), (iv): correct, subject to §1.2.
- Lemma 3.4: correct.
- Theorem 4.1 (a): correct.
- Remark after Theorem 6.3, that the expansion at fixed $j$ holds for every minus law: correct.
- Remark 7.4, that (LR) is not needed for identification: correct.

---

## 4. Novelty and significance

**Main contribution.** In my view it is Theorem B with Theorem C:
- a uniform local description of the occupation count across the big-jump zone and the boundary layer by one kernel, with the exact coefficient $\gamma$ at bounded $j$;
- the correct censored-run term;
- a ratio-form statement valid up to the endpoint;
- exact, essentially sharp criteria for how the first run enters each zone.

This is new as a theorem. It uses the standard toolkit (giant-run decomposition, truncated Fuk–Nagaev bounds, local limit theorems), but the bookkeeping for a renewal functional cut at a fixed horizon is genuinely more delicate than for sums of a fixed number of variables. The second-order boundary layer (Theorem 6.3), with its exact coefficient and the antimode law $T_-(j^*_N)\sim2\alpha_+s/N$, is a pleasant and, as far as I know, new result.

**What an EJP referee would regard as routine:**
- Theorem A on the window, which follows from Doney, Berger and Gnedenko, as the author acknowledges; the whole-row extension is short.
- Lemma 2.1 and the positivity of stable densities.
- Theorem D (a)–(c), a direct corollary of Theorem C (b) plus a comparison of exponents. Part (d) adds a constant.
- Theorem F (a), immediate from Theorem 4.1 (a) and renewal inversion.
- Corollary 5.10 (no universal trim), a neat construction but a small point.

**Significance.** The paper answers the physics literature's informal infinite-density picture with theorems and makes the role of the preparation precise. That is of real interest to EJP readers working on renewal theory and heavy tails. It would be more convincing if the core (Sections 4–5 and 6.2–6.3) were not buried in a long manuscript.

---

## 5. Length

At 62 pages the paper is roughly twice the length its new content needs. Page estimates refer to the current PDF.

| Item | Suggestion | Saving |
|---|---|---|
| Lemma 2.1 proof (sec_setting.tex:119–240) | Positivity of $\alpha$-stable densities for $\alpha\in(1,2)$ and continuity in parameters are classical (Zolotarev; Sato, Ch. 3). Keep the statement and cite. | ~1.5 pp |
| Lemma 3.6, Lemma 5.3 (i)–(iii), Lemma 6.2 | Each proves a uniform tail or equicontinuity of $\{h_N\}$ again. Merge into Lemma 2.1. | ~1 p |
| Lemma 3.2 (i) normalization (sec_bulk.tex:76–112) | Classical (Feller XVII.5; BGT 8.3). Keep only the identification of $K_\alpha$. | ~0.7 p |
| Bulk proof (Section 3.4) | The six-step outline, Step 6, and the "three regimes" paragraph (sec_bulk.tex:389–399, 602–636) restate one another. If Berger's Theorem 3.3 applies, prove only the uniform bound and the remote bins. | 2–4 pp |
| Final-run identity, cost count, Table 1 numerics, Remark 4.11 numerics | Move to the verification section. | ~1 p |
| Remark 4.11, second paragraph (sharper factor than $\lambda_N$) | Sketch without proof; cut or reduce to one sentence. | ~0.4 p |
| Remark 4.13 ((LR) discussion) | Shorten to the two weaker conditions and the junction remark. | ~0.4 p |
| Theorem 5.1 (c), window criterion, sufficiency under (LR) for both signs (sec_preparation.tex:574–653) | Interesting but peripheral; state it as a remark with a sketch, or move it to an appendix. | ~1.3 pp |
| Remark 5.11 and its verification | Replace by a three-line table of indices. | ~0.6 p |
| Theorem 6.3 and Proposition 6.6 | Prove the uniform version once and deduce the fixed-$j$ statement. | ~0.7 p |
| Lemma 6.4 (uniform local big jump) | Known under (LR) for $r\le n^{1-\eta}$ (Denisov–Dieker–Shneer, Theorem 9.1 and related local results). Cite, or shorten. | ~0.8 p |
| Lemmas 4.3 and 6.5 | Classical Fuk–Nagaev and Chebyshev bounds; cite. | ~0.5 p |
| Theorem 7.1 (b) proof, and the example after it | Reduce to "Theorem 5.1 (d) plus inversion". | ~0.8 p |
| Remark 7.4, last sentence | Delete (unproved). | — |

The total saving is about 12–15 pages. That would bring the paper to about 45–50 pages without losing any theorem.

---

## 6. Specific corrections

### problem131_levy.tex
- **31–32.** Remove the `\proofpending` macro and the "drafting aid" comment before submission. **73:** `sec_verify.tex` is a placeholder. Several statements in the body cite it, or depend on unpublished computations:
  - Figure 1 caption;
  - Remark 4.11 numbers;
  - the stationary check after Corollary 5.9;
  - the convergence numbers for $C(j)/j$ after Theorem 6.3;
  - the Frenk-ratio numbers;
  - Table 1.

  The paper cannot be accepted until the verification section exists or these statements are removed.
- **80.** `\bibliographystyle{abbrv}` does nothing next to a hand-written `thebibliography`; remove it.
- **Bibliography.** Five entries are never cited: `bvb2024`, `erickson1970`, `garsialamperti1962`, `sera2024`, `yamazato1978`. Cite them or remove them.
- **248–250.** The key `sera2024` is used for a 2026 article; harmless, but tidy it. Check the volume, year and pages of Sera (ETDS **46** (2026)).
- **210–212.** Check the arXiv number and title of Melbourne–Pène–Terhesiu.
- **232–233.** `paperD` is "in preparation". EJP referees generally dislike citations to unavailable work. Give an arXiv number or drop the reference.
- **44–62 (abstract).** See §2 (a), (b), (d), (e), (g).

### sec_intro.tex
- **15–16, 68–69.** Add the $\theta_{+,N}\to0$ gap; see §2 (c).
- **88–92.** Notation clash between $\kappa_+$ here (the fresh kernel, $\kappa_+(0)=1$) and $\kappa_+$ in (5.2) (prepared, $\kappa_+(0)=0$).
- **96–97.** "$\sim$" at $\kappa(j)=0$; see §2 (h).
- **99–102.** See §2 (a), (b).
- **113–117.** See §2 (f).
- **132.** A sentence ends and "Theorem" begins on the same source line. It renders fine but is hard to edit.
- **135–144.** Add "for a fresh plus start".
- **156–161.** The RDHB positioning needs correction; see §2.
- **185–190.** Make clear which part of Theorem A is new beyond Berger's Theorem 3.3.
- **190–195.** The Melbourne–Pène–Terhesiu comparison: add "in the i.i.d. setting".

### sec_setting.tex
- **56–58, 65.** (LR) should be stated independently, and the implication (LR) ⇒ (RV) is by the representation theorem; see §1.1.
- **42.** $K^\sigma_m(b)$ overloads $K$, which is also used for $K_\alpha$, the zone constant $K$, $K_0$, $K_1$ and $C_{\rm K}$. Consider $\Gamma^\sigma_m(b)$ or $N^\sigma_m(b)$.
- **420–424.** $A_t(k)$ and $B_t(k)$ clash with the occupation count $A_N$ and the scale $B_N$. This is the most confusing overload in the paper; rename, for instance to $a_t(k)$ and $b_t(k)$, or $\alpha_t$ and $\beta_t$.

### sec_bulk.tex
- **184–185.** $\rho_\sigma$ (the supremum of $a(m)/a(m-1)$) clashes with $\rho_i$ (Section 4), $\rho(R)$ (line 537) and $\rho_\sigma$ (the preparation index, Section 6).
- **393.** The outline's threshold $m\le\varepsilon N/(8\max\mu)$ differs from the one in Step 2, which uses $\beta=1/2$ with $m\le k_-<\varepsilon N$. Align them.
- **527.** $\kappa=s/(2c_1\mu_{\max})$ clashes with the boundary kernel $\kappa$; rename it.
- **624–636.** Step 6 contains no argument; merge it into a closing remark.

### sec_bigjump.tex
- **66 vs sec_preparation.tex:33.** $\hat G_N$ and $\widehat G_N$ for the same function.
- **109–111.** Good. Repeat this in the introduction.
- **346–348.** Write out the minus-start case.
- **366.** "$|I_h|\ge m/3$" should be halves of sizes $\lfloor m/2\rfloor$ and $\lceil m/2\rceil$, to match $a_+(\lfloor m/2\rfloor)$.
- **659.** "$B_N=O(N^{(1+1/\alpha_*)/2})$" is an odd way to say $\lambda_NB_N=o(N)$. State $B_N\in\mathrm{RV}_{1/\alpha_*}$, so $B_N\log N=o(N)$.
- **729–732.** See the RDHB and VBB positioning in §2.
- **799–814 and 861–868.** Reword the conclusion of Example 4.12; see §2 (a).
- **878–884.** "The first is window regularity … The second is …" is ambiguous. The nearest antecedents are the two options in the previous sentence ("assume $f_-(1)>0$" and "keep only the additive form"), not the "two weaker conditions" mentioned earlier. Reorder the sentences.

### sec_preparation.tex
- **15.** $L^\sigma_N(b)$ (the defect) clashes with $L_k$ and $L$; consider $\mathcal D^\sigma_N(b)$.
- **42–48.** Give (R$\nu$) a displayed definition with a label, since it is used in several theorems.
- **110–111.** Forward reference: use Lemma 7.2, not Theorem 4.1 (a).
- **114.** "(d) needs only (RV) and (SPAN)": (SPAN) is not used.
- **648–653.** "Under (LR) for both signs the preparation is invisible on every interior zone." Add "by the window criterion" and point to the sufficiency proof.

### sec_shape.tex
- **343.** "$\gamma=\eta/2$" clashes with the coefficient $\gamma(j)$; rename.
- **386.** $g_N(x)$ clashes with the stable densities $g_\sigma$; rename, for instance to $\phi_N$.
- **529 vs 697.** The theorem minimizes over $0\le j\le(1-p)N$, the table caption over $0\le j\le N/2$. This agrees only because $p=1/2$; say so.
- **586–596.** $\theta$ is reused for $(1/\mu_--m_*)/3$, and $\theta_\delta$ at line 660, beside $\theta_{\sigma,N}$; rename.
- **686–692.** Table 1 lists $N=8000$, but the planned certified list in the placeholder stops at 4000. Make the two consistent.
- **Remark 6.9.** Useful. It could replace the long "picture" paragraph in the introduction.

### sec_inverse.tex
- **9.** (SPAN) is not needed for (a); see §3.
- **23–25.** Replace the defect hypothesis with $\nu_+(n)=o(T_+(n))$.
- **116.** Cite the precise result in Embrechts, Klüppelberg and Mikosch.
- **191–196.** Delete the unproved claim.

---

## Three questions for the author

1. **The window $KB_N\le k-pN\le K\lambda_NB_N$ when $\theta_{+,N}\to0$.** Can you prove the natural two-term statement $P_N(k)=(1+o(1))\bigl(B_N^{-1}h_N(x_{N,k})+G_N(k)\bigr)$ there? Or, if not, can you at least say which of the two terms dominates as a function of $k$? Without this the "whole row" description has a hole precisely in the case of unequal indices that the paper emphasises.
2. **What exactly is necessary in the big-jump zone under (RV)?** Example 4.12 shows that the pointwise kernel fails. Does a window-averaged kernel, $\gamma(j)\cdot B_N^{-1}\sum_{|d|\le B_N}f_+(\lfloor L_k\rfloor+d)+T_+(\lfloor L_k\rfloor)\kappa(j)$ or similar, hold under (RV) and (SPAN) alone? If so, the claim "(LR) is necessary" should be replaced by that theorem. If not, what is the obstruction?
3. **Which part of Theorem A is genuinely beyond Berger (2019, Theorem 3.3) and Doney (1991)?** In particular, does Berger's multivariate local limit theorem cover marginals with different indices and oscillating scale ratios? If it does, would you agree to replace Section 3.4 by a citation for the window plus a short proof of the uniform bound and of the remote bins?
