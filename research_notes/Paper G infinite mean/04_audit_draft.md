# Paper G draft: audit of the four additions

2026-10-25. Adversarial check of four items added to `kagey-problems/problem131/paperG` while drafting, which `02_audit.md` did not cover, plus a check that the main statements of the draft match the audited versions. For each item: a claim card, my own derivation of the critical step (done before reading the draft's proof), then each implication checked in turn. Read-only on the paper.

Scratch file (outside the repo): `pitch.py` in the session scratch folder `...\scratchpad\auditG4\`, run with `py -I` and mpmath at 40 digits.

## Verdicts

| Item | Verdict |
|---|---|
| 1. Corollary `cor:lower` (lower half of the local law, RV and SPAN only) | **Proved as written** |
| 2. Proposition `prop:pitchfork` (minima near $\alpha_c$) | **Proved as written**, with one sentence to tighten (2.3, step 4). Formulas and all quoted numbers confirmed numerically |
| 3. Local law for the position $W_N=2A_N-N$ | **Correct after a stated restriction**: the start must be a fresh or mixed fresh start (or one covered by Thm `thm:initial`(c)). The sentence states only (RV), (SPAN), (SRT$_\pm$). The comparison with ZDK Eq. (61) is correct |
| 4. Appendix `app:routine` | **Proved as written**, with two small wording points in Lemma `lem:rv-facts`(i) (4.1) |
| Main statements versus `02_audit.md` | **Match**, with two sentences that drop (LB$_\pm$) (Section 5) |

Nothing is refuted.

---

## 1. Corollary `cor:lower`

**Claim card.** Assume (RV$_\alpha$), (SPAN), and a fresh start of either sign. Then
(a) for all $0<x_1<x_2<1$, $\liminf_N\inf_{x_1N\le k\le x_2N}(NP_N(k)-L_{\alpha,b}(k/N))\ge0$;
(b) if (SRT$_+$) or (SRT$_-$) fails, then $\limsup_N NP_N(\lfloor xN\rfloor)>L_{\alpha,b}(x)$ for every $x\in(0,1)$.

**My derivation of the critical step.** All terms of the fresh-plus identity are nonnegative, so $P_N(k)\ge\mathrm I_{\rm m}+\mathrm{II}_{\rm m}$ (medium $m$ only). The medium-range limit uses only Gnedenko's LLT (needs RV and SPAN), Lemma `lem:kernel-limit` (uses Gnedenko, (R1), (R2), (R3)) and $a_{m_N(t)}/N\to t^{1/\alpha}$ (Lemma `lem:rv-facts`(iii)). None of these uses SRT or LB. So $NP_N(k)\ge\Lambda_\delta(k/N)+o(1)$ uniformly on $[x_1N,x_2N]$. Then $NP_N(k)-L(k/N)\ge-\sup_{[x_1,x_2]}(L-\Lambda_\delta)+o(1)$. Let $N\to\infty$, then $\delta\to0$.

**Implications checked.**
1. Medium-range estimate (eq. `medium`) is proved without SRT. I re-read the proof: the inputs are Lemma `lem:cd`(i), Lemma `lem:kernel-limit`, the continuity of $h$ and the Riemann sum. Correct.
2. $\Lambda_\delta\uparrow L$ uniformly on $[x_1,x_2]$. $\Lambda_\delta$ is continuous in $x$ (integral of a continuous function over a compact $t$-range), $L$ is continuous, and the convergence is monotone, so Dini applies. Correct.
3. For the fresh minus start, the index shift does not touch the medium range. Correct.
4. Part (b). If $\limsup_N NP_N(\lfloor xN\rfloor)\le L(x)$, part (a) at $k=\lfloor xN\rfloor$ gives $\liminf\ge L(x)$, so $NP_N(\lfloor xN\rfloor)\to L(x)$. That is (i) of Thm `thm:local` with $x_0=x$, and (i)$\Rightarrow$(iii) gives both SRTs. The contrapositive is (b). Correct, and it holds at every $x$, as stated.
5. The intro paraphrase ("the failure ... shows up as an excess at every interior point") matches (b).

**Verdict: proved as written.** Remark: by convexity the same holds for any mixed fresh start; the draft does not claim this and need not.

---

## 2. Proposition `prop:pitchfork`

**Claim card.** For $\alpha>\alpha_c$ let $t^*_\alpha>0$ be the zero of $\chi(t)=\cosh\alpha t+\cos\pi\alpha-\alpha\sinh(\alpha t)\coth(t/2)$. As $\alpha\downarrow\alpha_c$,
$t^*_\alpha\sim\bigl(3(2\alpha^2-1-\cos\pi\alpha)/(\alpha^2(1-\alpha^2))\bigr)^{1/2}\sim\bigl(12(1+\frac\pi2\sin\frac{\pi\alpha_c}2)(\alpha-\alpha_c)/(\alpha_c(1-\alpha_c^2))\bigr)^{1/2}$, and the minima are at distance $t^*/4+O(t^{*3})$ from $1/2$.

### 2.1 My derivation

Expand at $t=0$: $\cosh\alpha t=1+\frac{\alpha^2t^2}2+O(t^4)$; $\sinh\alpha t=\alpha t+\frac{\alpha^3t^3}6+O(t^5)$; $\coth(t/2)=\frac2t+\frac t6+O(t^3)$. So
$\alpha\sinh(\alpha t)\coth(t/2)=2\alpha^2+t^2(\frac{\alpha^2}6+\frac{\alpha^4}3)+O(t^4)$ and
$\chi(t)=(1+\cos\pi\alpha-2\alpha^2)+\frac{\alpha^2(1-\alpha^2)}3t^2+O(t^4)$.
This gives $\kappa_\alpha=\frac13\alpha^2(1-\alpha^2)$, as in the draft. Cross-check through the draft's route: $n'(t)=(1-\alpha^2)\sinh\alpha t\sinh t\approx(1-\alpha^2)\alpha t^2$, so $n\approx\frac13\alpha(1-\alpha^2)t^3$, and $G'=\alpha n/(2\sinh^2(t/2))\approx2\alpha n/t^2=\frac23\alpha^2(1-\alpha^2)t$, which integrates to $\kappa_\alpha t^2$. Consistent.

Setting $\chi(t^*)=0$: $t^{*2}\sim-\chi(0+)/\kappa_\alpha=3(2\alpha^2-1-\cos\pi\alpha)/(\alpha^2(1-\alpha^2))$.

Second form: $-\chi(0+)=2(\alpha-\cos\frac{\pi\alpha}2)(\alpha+\cos\frac{\pi\alpha}2)$ (using $1+\cos\pi\alpha=2\cos^2\frac{\pi\alpha}2$). The first factor vanishes at $\alpha_c$ with derivative $1+\frac\pi2\sin\frac{\pi\alpha_c}2$; the second tends to $2\alpha_c$. So $-\chi(0+)\sim4\alpha_c(1+\frac\pi2\sin\frac{\pi\alpha_c}2)(\alpha-\alpha_c)$, and dividing by $\kappa_{\alpha_c}=\alpha_c^2(1-\alpha_c^2)/3$ gives $12(1+\dots)(\alpha-\alpha_c)/(\alpha_c(1-\alpha_c^2))$. Matches.

Last claim: $1/(1+e^t)=\frac12-\frac12\tanh(t/2)=\frac12-\frac t4+\frac{t^3}{48}-\dots$. Matches.

### 2.2 Numerical spot check (own script)

$\alpha_c=0.59461164405683558\ldots$ (root of $\cos(\pi\alpha/2)=\alpha$). $t^*$ by bisection on $\chi$; the minimum of $L_{\alpha,1}$ located independently by bisection on a numerical derivative of $L$ in $x$.

| $\alpha$ | $t^*$ | first form $/t^*$ | second form $/t^*$ | $x_{\min}$ | $1/(1+e^{t^*})$ | $(\frac12-x_{\min})/(t^*/4)$ |
|---|---|---|---|---|---|---|
| $\alpha_c+10^{-8}$ | 0.000840519 | 1.000000 | 1.000000 | 0.499790 | 0.499790 | 1.000000 |
| $\alpha_c+10^{-6}$ | 0.00840517 | 1.000001 | 1.000002 | 0.497899 | 0.497899 | 0.999994 |
| 0.5947 | 0.0789956 | 1.000081 | 1.000144 | 0.480261 | 0.480261 | 0.999480 |
| 0.60 | 0.611653 | 1.004941 | 1.008719 | 0.351682 | 0.351682 | 0.969947 |
| 0.61 | 1.01764 | 1.014070 | 1.024588 | 0.265487 | 0.265487 | 0.921790 |
| 0.70 | 2.37602 | 1.098801 | 1.148400 | 0.085020 | 0.085020 | 0.698614 |

Also $(\chi(t)-\chi(0+))/t^2$ at $\alpha=0.6$, $t=10^{-3}$, is $0.0768000002$, against $\kappa_{0.6}=0.0768$.

The draft's numbers are all confirmed: at $\alpha=0.5947$, $t^*=0.0790$ and the first form is within $0.0081\%<0.01\%$; at $\alpha=0.61$, $t^*=1.018$, the first form is within $1.41\%<1.5\%$, and the minima are at $0.2655$ and $0.7345$. Both ratios tend to 1 at the predicted rate ($1-$ratio scales like $\alpha-\alpha_c$).

### 2.3 Implications checked

1. Expansion of $n$, $G'$, $\kappa_\alpha$: correct (2.1).
2. "$|r(t,\alpha)|\le Ct^2$ for $|t|\le1$ and $\alpha$ near $\alpha_c$, since $\chi$ is analytic near $(0,\alpha_c)$ and even in $t$." True, but the reason as written is local; the bound on all of $|t|\le1$ needs analyticity on a neighbourhood of $[-1,1]\times\{\alpha_c\}$. That holds: $\sinh(\alpha t)\coth(t/2)$ is analytic for $|t|<2\pi$. Wording only.
3. $\chi(0+)\uparrow0$ as $\alpha\downarrow\alpha_c$: $\frac{d}{d\alpha}(1+\cos\pi\alpha-2\alpha^2)=-\pi\sin\pi\alpha-4\alpha<0$, and it vanishes at $\alpha_c$. Correct.
4. $t^*\to0$. The draft says "By the expansion it tends to 0". From $\kappa t^{*2}(1+r)=-\chi(0+)\to0$ this needs $1+r$ bounded below on $(0,1)$, which $|r|\le Ct^2$ does not give if $C\ge1$. The fix is the argument the draft already uses for $t^*<1$: for any fixed $\epsilon\in(0,1)$, $\chi(\epsilon)-\chi(0+)=G(\epsilon)-G(0+)>0$ is continuous in $\alpha$, so $\chi(\epsilon)>0$ for $\alpha$ near $\alpha_c$ and $t^*<\epsilon$. Once $t^*\to0$, $r(t^*,\alpha)=O(t^{*2})\to0$ and the first equivalence follows. **Smallest missing implication, one sentence.**
5. $\chi(1)>0$ near $\alpha_c$ and the zero is unique (Theorem `thm:shape`): correct.
6. Second equivalence and the $x$-distance: correct (2.1).

Also checked in the surrounding text: as $\alpha\to1$, $\chi(t)\to\cosh t-1-\sinh t\coth(t/2)=\cosh t-1-(1+\cosh t)=-2$ (using $\sinh t\coth(t/2)=2\cosh^2(t/2)$). Correct.

**Verdict: proved as written**, after one added sentence in step 4.

---

## 3. Local law of the position $W_N$

**Claim card.** Under (RV$_\alpha$), (SPAN), (SRT$_\pm$): $N\Prob(W_N=v)=L_{\alpha,b}((1+v/N)/2)+o(1)$ uniformly over $v\equiv N\pmod2$ with $v/N$ in compacts of $(-1,1)$; the limit density of $W_N/N$ is $\frac12L((1+\xi)/2)$; for $b=1$ this is ZDK Eq. (61).

**My derivation.** $\{W_N=v\}=\{A_N=(N+v)/2\}$, which needs $v\equiv N\pmod 2$. With $k=(N+v)/2$, $k/N=(1+v/N)/2$, and $v/N\in[-1+2x_1,\,2x_2-1]$ iff $k/N\in[x_1,x_2]$. Thm `thm:local`(ii) gives the claim. The density: if $A_N/N\Rightarrow X$ with density $L$, then $2X-1$ has density $\frac12L((1+\xi)/2)$.

ZDK check (I read Eq. (61) in the arXiv text, 1410.5100): $\Phi(\xi)=\frac{\sin\pi\gamma}\pi\,\frac{|\xi-1|^\gamma|\xi+1|^{\gamma-1}+|\xi+1|^\gamma|\xi-1|^{\gamma-1}}{|\xi-1|^{2\gamma}+|\xi+1|^{2\gamma}+2|\xi-1|^\gamma|\xi+1|^\gamma\cos\pi\gamma}$. With $|\xi+1|=2x$, $|\xi-1|=2(1-x)$ the numerator is $2^{2\gamma-1}x^{\gamma-1}(1-x)^{\gamma-1}$ and the denominator $2^{2\gamma}[\dots]$, so $\Phi=\frac12L_{\gamma,1}(x)$. Correct.

**Implications checked.**
1. Lattice and parity: correct.
2. Uniformity transfer: the map $v\mapsto k$ is affine, so compacts correspond. Correct.
3. **Start.** Thm `thm:local` is proved for fresh starts, and the paragraph extends it to mixed fresh starts. For a general initial run the local law can fail even with $D<\infty$ (Thm `thm:initial`(e)), so the position law does too. The displayed sentence lists only (RV), (SPAN), (SRT$_\pm$). It sits right after the sentence about mixed fresh starts, so the intent is clear, but the hypothesis should be written in: "for a fresh or mixed fresh start" (or any start for which (ii) holds, e.g. Thm `thm:initial`(c)).

**Verdict: correct after the stated restriction** (fresh or mixed fresh start).

---

## 4. Appendix `app:routine`

### 4.1 Lemma `lem:rv-facts`(i): (R4)

*First sum.* $\phi(w)=wT(w)$ is RV with index $1-\alpha>0$ and $\inf_{w\ge1}\phi>0$ ($\phi\ge T(x_0)$ on $[1,x_0]$ since $T$ is nonincreasing, and $\phi\to\infty$). Potter for a positive index: $\phi(y)/\phi(x)\le2(y/x)^{(1-\alpha)/2}$ for $x_0\le y\le x$. (R2) with $c=2$ gives $2^lT(2^{l-1})\le C\phi(2^l)$ for $l\ge1$. With $2^L\le x<2^{L+1}$, $2^l/x\le2^{l-L}$, so the terms with $x_0\le2^l\le x$ sum to $\le C\phi(x)\sum_{i\ge0}2^{-i(1-\alpha)/2}$. The rest is a constant $\le C\phi(x)$. Correct.

*Second sum.* The draft applies Potter "for $y\ge x\ge x_0$", but the first term with $2^l>x$ has $2^{l-1}\in(x/2,x]$, possibly below $x$. That term is $\le T(x/2)\le CT(x)$ by (R2), and the later terms have $2^{l-1}\ge x$. Wording only. For $1\le x<x_0$, $\sum_{l\ge1}T(2^{l-1})<\infty$ and $T(x)\ge T(x_0)>0$. Correct.

*Citation point.* The proof uses Potter's theorem in its power form (BGT Thm 1.5.6), which is stronger than (R2) as stated in Section `sec:rv`; Section `sec:rv` says (R4) follows from "(R1) and (R2)". Better: "(R2) and Potter's theorem". Wording only.

### 4.2 Lemma `lem:rv-facts`(ii)
A convergent sequence of finite numbers is bounded. Correct.

### 4.3 Lemma `lem:rv-facts`(iii)
- $m=m_N(t)$: $mT(N)\in(t-T(N),t]$, so $mT(N)\to t$; $m\to\infty$, so $mT(a_m)\to1$; hence $T(a_m)/T(N)\to1/t$. Correct.
- Subsequence with $a_m/N\to\lambda$. For $\lambda\in(0,\infty)$, (R1) (uniform convergence) gives $\lambda^{-\alpha}=1/t$. For $\lambda\in\{0,\infty\}$, Potter gives a ratio $\to\infty$ or $0$ (needs $a_m\to\infty$, true since $tT(a(t))\to1$ forces $a(t)\to\infty$). Correct.
- Uniformity: $t\mapsto a_{m_N(t)}/N$ is nondecreasing ($m_N$ nondecreasing in $t$, $a$ increasing), the limit $t^{1/\alpha}$ is continuous and strictly increasing; pointwise convergence of monotone functions to a continuous limit is uniform on compacts. Correct.

### 4.4 Lemma `lem:poisson`
$\mathrm{Im}(x+i\varepsilon-v)^{-1}=-\varepsilon/((x-v)^2+\varepsilon^2)$, so $-\frac1\pi\mathrm{Im}\,G=\Lambda*P_\varepsilon$. Near part: error $\le\sup_{|v-x|\le\eta}|\Lambda(v)-\Lambda(x)|$ (needs $[x-\eta,x+\eta]\subset(0,1)$, fine for small $\eta$), and $\int_{|u|\le\eta}P_\varepsilon\to1$. Far part $\le\sup_{|u|>\eta}P_\varepsilon\cdot\int\Lambda\to0$. Correct. In Prop. `prop:lambda` it is applied with $\Lambda$ continuous on $(0,1)$ and integrable (total mass 1), so the hypotheses hold.

### 4.5 Normalization of the minus sums
$mT_-(a_mz)=\frac{T_-}{T_+}(a_mz)\cdot\frac{T_+(a_mz)}{T_+(a_m)}\cdot mT_+(a_m)\to b\,z^{-\alpha}$. For $\alpha<1$ and positive summands this is the classical criterion for convergence without centering to the positive stable law with Lévy tail $bz^{-\alpha}$, Laplace exponent $b\Gamma(1-\alpha)\lambda^\alpha$, i.e. $b^{1/\alpha}Z$. Ibragimov-Linnik Thm 4.2.1 is stated for any norming $B_n$ under which the sums converge, with the maximal span, which is 1 under (SPAN). Correct.

**Verdict for the appendix: proved as written**, with the two wording points in 4.1.

---

## 5. Main statements against `02_audit.md`

| Audited point | Draft | Status |
|---|---|---|
| Aging-type start incomplete; needs (LB$_\pm$) and the near-diagonal bound | Stated as Conjecture `rem:aging`, hypotheses include (LB$_\pm$), and the missing near-diagonal bound is written out; intro calls it a conjecture | Matches |
| Exact sign-change count unproved | Conjecture `conj:count`; Thm `thm:signs` is only a lower bound; the abstract says "a lower bound" | Matches |
| $j=0$ end value is $\lim Q_\pm(N)/T_\pm(N)$, assumed to exist | Thm `thm:signs` defines $\kappa_\pm(0)$ as these limits and assumes they exist and are finite; text after (f) and after Thm `thm:signs` says the same | Matches |
| Thm 1 (local law) hypotheses RV, SPAN, fresh start | Thm `thm:local` same | Matches |
| Thm 2(a) RV only; (b) LB$_+$ and SRT$_-$; (c) LB$_\pm$ and pure powers | Thm `thm:ends` same | Matches |
| Thm 3: (c),(d) need (LB$_\pm$); (d) needs $u_\pm>0$; (f) RV only | Thm `thm:initial` puts (LB$_\pm$) in (c), (d) and $u_\pm>0$ in (d); (f) says "Assume only (RV), (SPAN)" | Matches |
| Thm 3(b): $\nu_\pm(n)=o(1/(nT_\mp(n)))$ | $nT_+(n)\nu_\pm(n)\to0$; equivalent since $T_-\asymp T_+$ | Matches |
| Thm 4(a) shape, $b=1$ only | Thm `thm:shape` for $b=1$; Remark `rem:unequal` says no proof for $b\ne1$ | Matches |

Two sentences drop the (LB$_\pm$) restriction of Thm `thm:initial`(c):
1. Intro, Section `sec:intro-initial`: "Every fixed initial run with $n\nu_\pm(n)\to0$ leaves the local law and the end layers unchanged." The end-layer half is (f) and needs only RV; the local-law half is (c) and needs (LB$_\pm$). Add "under Doney's condition" (the earlier sentence in the same paragraph has it).
2. After Thm `thm:initial`: "Every initial run with a regularly varying tail ... and an eventually monotone mass function satisfies (c), whatever its index, so it changes neither the bulk nor ..." and the example $\nu_\pm(n)\propto n^{-1-\gamma}$ "the local Lamperti law still holds". Both need (LB$_\pm$), which holds for the zeta law used in Section `sec:verify`, but should be said.

Minor: the abstract's "lower bound on the number of local extrema" counts sign changes of the differences, which equal strict local extrema only when no two neighbouring values are equal (Section `sec:signs` says this).

---

## 6. Fixes applied (2026-10-25)

1. `prop:pitchfork` (`sec_shape.tex`). Replaced "By the expansion it tends to 0" with the argument used for $t^*<1$. For each fixed $\varepsilon\in(0,1)$, $\chi(\varepsilon)-\chi(0+)=G(\varepsilon)-G(0+)>0$ is continuous in $\alpha$, so $t^*_\alpha<\varepsilon$ near $\alpha_c$. Then $r(t^*_\alpha,\alpha)=O((t^*_\alpha)^2)\to0$ is stated before the first equivalence. Closes 2.3, step 4.
2. Position law (`sec_local.tex`). The sentence now reads "for a fresh or mixed fresh start under (RV$_\alpha$), (SPAN) and (SRT$_\pm$)". Closes 3, item 3.
3. `lem:rv-facts`(i) (`sec_appendix.tex`, `sec_tools.tex`). The second sum now treats the first term with $2^l>x$ separately ($\le T(x/2)\le CT(x)$ by (R2)) before applying Potter to the later terms. The proof cites Potter's theorem as BGT Thm 1.5.6, and Section `sec:rv` now says (R4) follows from "(R2) and Potter's theorem" instead of "(R1) and (R2)". Closes 4.1.
4. (LB$_\pm$) in the initial-run sentences. Intro (`sec:intro-initial`) now opens the sentence with "Under Doney's condition". After Thm `thm:initial` (`sec_initial.tex`), "Under (LB$_\pm$)" is added to the regularly varying initial-run sentence and to the $\nu_\pm(n)\propto n^{-1-\gamma}$ example. The abstract states no initial-run sufficient condition explicitly, so it needs no change. No other sentence in the introduction drops the hypothesis. Closes Section 5.

Rebuilt with pdflatex three times. 27 pages, no undefined references, no overfull boxes, the only warning is the class's `pagebackref`. `py -I verify_all.py` passes (4 scripts). The abstract wording point on local extrema was left as is.
