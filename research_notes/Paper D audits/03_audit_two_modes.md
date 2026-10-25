# Audit 03: the two mode theorems of Paper D

Date: 2026-10-25. Read-only audit of `kagey-problems/problem131/paperD`
(journal file `problem131_memory.tex`).

Scope:
- Theorem 4.2 (`thm:two-modes`, `sec_bulk_applications.tex`) and its lemmas in
  Appendix F (`app_modes.tex`: `lem:descartes`, `lem:sp-limit`, `lem:sp-derivative`).
- Its finite input, Theorem 3.16 (`thm:five-blocks`, `sec_erw_shape.tex`), with
  `lem:D-rec`, `lem:interleave`, `lem:level-one` and the proof in `app_erw_signs.tex`.
- Theorem 4.3 (`thm:two-modes-near-one`).
- The statement of the GLRS conjecture and the claims of what is settled.

Sources read: local copies in
`research_notes/Paper D independent JTP review/literature_erw/`, namely
GLR arXiv:2308.14630v2 (the AIHP paper), GLRS arXiv:2409.06836v1, and
Trinas and Valle arXiv:2609.14753v1.

## Verdicts

| Result | Verdict |
|---|---|
| Theorem 3.16 (five blocks), part for $P_N$ | proved as written |
| Theorem 4.2 (at most two modes) | proved as written |
| Theorem 4.3 (two modes for $a\ge 39/40$) | proved as written |
| Text around them | two wording fixes recommended (Section 5) |

No counterexample and no missing implication was found. Every step below was
checked by hand. The only numerical inputs (the constants of Theorem 4.3) were
recomputed at 50 digits.

## 1. Claim cards

**Theorem 3.16.** Objects: $A_t$ = number of $+1$ steps of the fair-start
elephant walk with $\Prob(X_{t+1}=+1\mid A_t=b)=r_t(b)=\varepsilon+cb/t$,
$c=1-2\varepsilon$; $P_N(k)=\Prob(A_N=k)$; $D_N(k)$ its second difference.
Hypotheses: $N\ge3$, $0<\varepsilon<\frac12$. Conclusion:
$\operatorname{sp}(D_N(1),\dots,D_N(N-1))\preceq(+,-,+,-,+)$.

**Theorem 4.2.** Objects: $a\in(\frac12,1)$, $\varepsilon=(1-a)/2$,
$\mathcal L^\circ_a=\lim S_N/N^a$ with fair first step, $g_a$ its density.
Hypothesis: only $a\in(\frac12,1)$. Conclusion: exactly one of (a) $g_a$
nondecreasing on $(-\infty,0]$ and nonincreasing on $[0,\infty)$; (b) some
$c>0$ with $g_a$ nondecreasing on $[0,c]$, nonincreasing on $[c,\infty)$ and
$g_a(0)<g_a(c)$. In (b), $g_a$ is not unimodal. Strict local maxima are only
$0$ in (a), only $\pm c$ in (b); if $g_a$ is constant on no interval, the same
holds for all local maxima.

**Theorem 4.3.** Hypothesis: $\frac{39}{40}\le a<1$. Conclusion: case (b).

## 2. Theorem 3.16 (input to 4.2)

Own derivation, then comparison with the appendix.

- `lem:D-rec`. Substituting $P_{t+1}(a)=(1-r_t(a))P_t(a)+r_t(a-1)P_t(a-1)$ at
  $a+1,a,a-1$ gives the four coefficients
  $1-r_t(a+1),\ 3r_t(a)-2,\ 1-3r_t(a-1),\ r_t(a-2)$. Since $r_t$ is affine in $b$,
  $2r_t(a+1)+r_t(a-2)=3r_t(a)$ and $r_t(a+1)+2r_t(a-2)=3r_t(a-1)$, which gives
  \eqref{eq:D-rec}. Valid for all integers $a$ because $P_t$ vanishes off
  $\{0,\dots,t\}$. Correct.
- `lem:interleave`. Each $\eta_i$ is inserted directly between its two
  parents, which are adjacent in $w$, so a nonzero $\eta_i$ sits next to an
  entry of its own sign. Correct.
- Lists $\mathcal Z_t$. Length $2N-t-1$ checked. Index bookkeeping for
  $\mathcal Z_t\to\mathcal Z_{t+1}$: positions $1..N-t$ are copies ($A=1,B=0$),
  positions $N-t+1..N-2$ are $D_{t+1}(b)$, $2\le b\le t-1$, with parents
  $D_t(b-1),D_t(b)$ at positions $N-t+b-1,\,N-t+b$, positions $N-1..2N-t-2$ are
  right-shifted copies ($A=0,B=1$). Coefficients
  $r_t(b-2)\ge\varepsilon$, $1-r_t(b+1)\ge1-\varepsilon-c=\varepsilon$. Correct.
- `lem:level-one`. Rederived: $P_2(0)=(1-\varepsilon)/2$, $P_2(1)=\varepsilon$,
  $\xi_2=2\varepsilon/(1-\varepsilon)$; the recursion for $\xi_t$; the bound
  $\xi_t<\varepsilon t/c$; $\sigma_t=(\varepsilon-c/t)(\xi_t-2)P_t(0)$ from
  $D_t(0)=P_t(1)-2P_t(0)$; $s_2=1-3\varepsilon$; partial-sum sign argument in
  both cases $\varepsilon<\frac13$ and $\varepsilon\ge\frac13$. Second claim:
  $s_3=(1-\varepsilon)^2-\frac12$ and, when $s_3=0$,
  $s_4=-(5\varepsilon-1)/12\ne0$. All correct.
- The six cases for $\operatorname{sp}(\mathcal Z_3)$ are right.

The $f_N$ part and Theorem 3.17 (no holes) are not used by 4.2 and 4.3; I read
them but did not audit them to the same depth.

## 3. Theorem 4.2

**Step 1 (smoothing, Descartes).** $\varphi(y-z_k)=\varphi(y)e^{-z_k^2/2\sigma^2}
e^{yz_k/\sigma^2}$, so $V_N=\varphi\cdot F$ with exponents $z_k/\sigma^2$
strictly increasing and coefficients positive multiples of $D_N(k)$. So
$\operatorname{sp}(b)=\operatorname{sp}(D_N(1..N-1))\preceq\Pi_5$.
`lem:descartes`: the Rolle induction on $S(b)$ is the standard one; the
coefficient flip at a chosen sign change reduces $S$ by exactly one; the
sign list on the at most $S(b)+1$ zero-free intervals starts with the sign of
the first nonzero coefficient (behaviour at $-\infty$), so it is
$\preceq\operatorname{sp}(b)$. Zeros of $F$ at sample points are deleted by the
definition of sp, and touching zeros only merge blocks. The all-zero case is
handled. Correct.

**Step 2 ($N\to\infty$), lattice-to-continuum scaling.** $z_k=(2k-N)N^{-a}$,
spacing $\eta=2N^{-a}$, $S_N/N^a=z_{A_N}$ since $S_N=2A_N-N$. Summation by
parts over $k=-1..N+1$ gives $\sum_jP_N(j)\Delta\varphi(y-z_j)$ with
$z_{j\pm1}=z_j\pm\eta$: checked. Central-difference Taylor bound
$|\eta^{-2}\Delta\varphi-\varphi''|\le\eta^2\|\varphi''''\|_\infty/12$: correct.
Boundary terms: $D_N(-1)=P_N(0)$, $D_N(0)=P_N(1)-2P_N(0)$, and their mirrors,
total $\le\varphi(0)(6P_N(0)+2P_N(1))$: checked. $P_N(0)=\frac12(1-\varepsilon)^{N-1}$
and, from the displayed formula in the proof of `thm:dip` with
$\vartheta_j\le1$, $f_N(1)\le\varepsilon(N-1)(1-\varepsilon)^{N-2}$, so
$P_N(1)=\frac12(f_N(1)+f_N(N-1))\le\varepsilon N(1-\varepsilon)^{N-2}$.
(Small point: the paper says "the proof of Theorem~\ref{thm:dip} gives" this bound; it
follows from that proof's formula in one line but is not written there.)
Exponential decay beats $\eta^{-2}=N^{2a}/4$. Weak convergence
$S_N/N^a\to\mathcal L^\circ_a$ (a.s. by Bercu, Thm 3.7, plus mirroring) and
$\varphi''$ bounded continuous give $V_N(y)\to u''(y)$ pointwise. Correct.

**Lower semicontinuity (`lem:sp-limit`).** Direction is the right one: for
fixed sample points, entries with $v(y_i)\ne0$ eventually carry the limit's
sign, zeros of the limit are dropped, and a sublist has a sub-pattern. So the
limit's pattern is $\preceq$ that of $v_n$, hence $\preceq\Pi$. Zeros and flat
pieces of the limit can only shorten the pattern. Correct, and used both at
$N\to\infty$ (values) and at $\sigma\to0$ (increments, along any sequence
$\sigma_n\to0$).

**Step 3 (`lem:sp-derivative`).** Own check: with $u'(\pm\infty)=0$, pick
$y_0,y_{j+1}$ with $|u'|$ smaller than at $y_1,y_j$; the $j+1$ mean-value points
carry signs $(-1)^is$, $i=0..j$. $\preceq\Pi_5$ forces $j\le4$, and $j\le3$ when
$s=-$, so the $u'$ pattern is $\preceq\Pi_4$. Increments of $u$ are values of
$u'$ at increasing points. $u$ is smooth and $u'\to0$ by dominated convergence.
Correct.

**Step 4 ($\sigma\to0$).** Needs only that $g_a$ is bounded and continuous.
Source: GLR Thm 1.3 (arXiv v2): "For any $q\in[0,1]$, $a\in(\frac12,1)$, the
random variable $L_q$ is absolutely continuous ... Its density is a positive,
bounded, smooth function on $\mathbb R$." The case $q=\frac12$ is exactly
$\mathcal L^\circ_a$ (GLR (1.3), (1.6), with $a=2p-1$, $q=\Prob(X_1=1)$; matches
the paper's $p=1-\varepsilon$). This gives exactly what is used (more, in fact).
Correct.

**Step 5 (symmetry and the dichotomy).** Reflected point set: increments
$-d_{j-1},\dots,-d_1,(0),d_1,\dots,d_{j-1}$; the junction does not merge since
$-d_1$ and $d_1$ have opposite signs; so $2|p|$ entries $\preceq\Pi_4$, giving
$p\in\{(),(+),(-),(+,-)\}$. $(-,+)$ is excluded since a subsequence of $\Pi_4$
starting with $-$ has at most three entries. The construction of $c$ (rise
$y_1<y_2$, forced fall from integrability since $g_a(y_2)>g_a(y_1)\ge0$, no rise
after the fall, max on $[0,y_4]$ by continuity), the two "fall then rise"
contradictions, $g_a(0)<g_a(c)$, exclusivity, non-unimodality in (b), and the
local-maximum statements were each checked. Correct.

Flat pieces: the theorem does not exclude plateaus (a plateau at the top in
case (a), or an interval of maximizers in case (b)); it says so honestly in the
last sentence. See Section 5 for why this matters for the conjecture wording.

## 4. Theorem 4.3

**Moments.** GLR Thm 1.4: $m_1=1$, $m_2=\frac{c_1m_1^2}{2a-c_2}=\frac a{2a-1}$
($c_1=a$, $c_2=1$), $\E L_1^k=\frac{(k-1)!}{a\Gamma(ka)}m_k$. So
$\E L_1=1/\Gamma(1+a)$ and $\E L_1^2=1/((2a-1)\Gamma(2a))$. GLR Remark 2.13 and
Trinas and Valle (4.3) state the same two formulas: verified verbatim. Own
cross-check from $\E S_{n+1}^2=(1+2a/n)\E S_n^2+1$ and
$\sum_{m\ge0}\Gamma(m+1)/\Gamma(m+1+2a)=1/((2a-1)\Gamma(2a))$; numerically at
$a=0.7$, $n=2\cdot10^5$ the first moment agrees to $10^{-6}$ and the second to
the expected $O(n^{1-2a})$. The paper's $\mathcal L_a$ is GLR's $L_1$. The
paper's quote of TV (4.5), $\Var=2(1-a)+o(1-a)$, matches (TV write
$\varepsilon=1-a$).

**Gamma bounds.** $\log\Gamma$ convex, $\Gamma(1)=\Gamma(2)=1$ give
$\log\Gamma\le0$ on $[1,2]$; the tangent at $2$ with slope $\psi(2)=1-\gamma$
gives $\log\Gamma(y)\ge(1-\gamma)(y-2)$. Applied at $y=2-\delta$ and
$y=2-2\delta$ (both in $[1,2]$ since $a>\frac12$). So $1\le\mu\le M$ and
$v\le\E L^2-\mu^2\le\E L^2-1\le V$. Correct; numerically the tangent bound has
minimum gap $0$ (at $y=2$) on a 1001-point grid.

**Inequalities.** Case (a) makes $F(t)=2\int_0^tg_a$ concave with $F(0)=0$, so
$F(t)/t$ is nonincreasing: $\frac52F(\frac25)\ge\frac47F(\frac74)$. Cantelli
(one-sided Chebyshev) with $w=\mu-\frac25\ge\frac35$:
$F(\frac25)=\Prob(|\mathcal L_a|\le\frac25)\le\Prob(\mathcal L_a\le\mu-w)\le
v/(v+w^2)\le V/(V+9/25)$, using monotonicity in $v$ and $w$. Chebyshev:
$|\mathcal L_a|>\frac74\Rightarrow|\mathcal L_a-\mu|>\frac74-M>0$. Also
$|\mathcal L^\circ_a|\overset d=|\mathcal L_a|$. All correct.

**Numbers** (`py -I`, mpmath at 50 digits, scratch script `audit03/chk.py`), at
$\delta=1/40$:

| quantity | exact value | paper |
|---|---|---|
| $M$ | 1.0106256640 | $\le1.0107$ |
| $V$ | 0.0751202450 | $\le0.0752$ |
| $V/(V+9/25)$ | 0.1726424956 | $\le0.173$ |
| $1-V/(7/4-M)^2$ | 0.8625868638 | $\ge0.862$ |
| $\frac52F(\frac25)$ bound | 0.4316062391 | $\le0.433$ |
| $\frac47F(\frac74)$ bound | 0.4929067793 | $\ge0.492$ |

The rounded chain (0.0752, 1.0107 → 0.17279, 0.86241 → 0.4325, 0.49257) also
closes. Margin at $\delta=1/40$ is about $0.061$. Both bounds move the wrong way
as $\delta$ grows, so $\delta\le1/40$ suffices. Bisection shows this exact
argument works up to $\delta\approx0.028355$, i.e. $a\ge0.97165$; $39/40$ is a
safe rational choice inside that range. True values at $a=39/40$:
$\mu=1.010421$, $v=0.053294$, consistent with the bounds.

## 5. Conjecture wording and claims of what is settled

- The block quote of GLRS Remark 2.1(b) matches arXiv:2409.06836v1 word for
  word. I could not check the published EJP text (only an access page is in the
  local folder).
- The reading of the conjecture at $q=\frac12$ ("unimodal or bimodal") is
  correct, and "if the conjecture holds then $q(a)>0$ for $a\ge39/40$" is
  correct. "The threshold for $q=\frac12$ remains open, as does the conjecture
  for $q\ne\frac12$" is accurate.
- **Fix 1 (citation of the definition).** The paper defines unimodal as
  "nondecreasing then nonincreasing" and attributes it to "[GLRS, Section 2]".
  GLRS state their definition on p. 3 (Section 1) and in different words: "the
  unimodality of $L_1$ means that this function has a unique local maximum."
  Their proof (Section 2) uses stability under weak convergence (Dharmadhikari
  and Joag-dev, Thm 1.1), which is the paper's weak sense. Suggest citing
  Dharmadhikari and Joag-dev for the definition, or saying "the sense used in
  the proof of [GLRS, Theorem 1.1]".
- **Fix 2 (scope of "proves the case $q=\frac12$").** Under GLRS's literal
  wording (unique local maximum), Theorem 4.2 settles the case $q=\frac12$ only
  up to plateaus: a flat top in case (a), or intervals of maximizers in case
  (b), is not excluded, and the cited results give smoothness, not analyticity.
  The theorem statement is honest about this; the sentence after Theorem 4.3
  and the intro line should say "in the sense of Section 4.2" or "up to flat
  pieces". This is a wording point, not a gap in the proof.

## 6. What I could not check

- The published EJP and AIHP versions; all source checks use the arXiv
  versions (GLR v2, GLRS v1, TV v1). GLR theorem numbers 1.3, 1.4 are from v2.
- Bercu 2018 Thm 3.7 (a.s. convergence for $X_1=1$) was taken as standard and
  not reopened; GLR (1.3) states the same convergence.
- The remark `rem:modes-threshold` (numerical threshold $a_c\approx0.66881$) is declared unused in
  any proof and was not rerun.
