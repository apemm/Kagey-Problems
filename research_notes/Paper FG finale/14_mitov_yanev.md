# Mitov and Yanev (2001): what the paper proves

27 October 2026. Read in full from the JSTOR copy (stable URL https://www.jstor.org/stable/1428311, Adv. Appl. Probab. 33 (2001), 896–911, SHA-256 `0086a3fe7adbefeb796dec02e1f8911a03ab20e4078c1f61afc4c627faccc727`). Both papers cited it only generically. This note records what it contains so that the related-work sentences are exact.

## Object

An alternating renewal process with waiting periods $X_i\sim A$ and work periods $T_i\sim F$, independent, nonlattice. The studied quantity is
$$\sigma(t)=t-S_{N(t)}-X_{N(t)+1},$$
the signed age of the current period: $\sigma(t)>0$ is the spent part of the current work period, and $\sigma(t)<0$ is minus the residual part of the current waiting period. With $X_i\equiv0$ it is the spent lifetime of an ordinary renewal process. The paper does **not** study the occupation time $\int_0^t1\{\text{working}\}$, and it does not study point probabilities. The discrete-time case is deferred to Mitov, Serdica Math. J. 25 (1999), 19–40, which we have not read.

## Hypotheses

(A.2): $\bar A(t)\sim t^{-\alpha}L_A(t)$ with $\alpha\in(\tfrac12,1]$ and $A(t)-A(t-h)=O(1/t)$. (F.1): $m_F<\infty$, or (F.2): $\bar F(t)\sim t^{-\beta}L_F(t)$, $\beta\in(\tfrac12,1]$. The limit $c=\lim\bar A(t)/\bar F(t)\in[0,\infty]$ is assumed to exist. Two regimes:

- (H.1): (A.2) and $c=\infty$, with (F.1) or (F.2) and $\beta>\alpha$. The waiting period dominates. This is the analogue of our (DOM) with the roles of the signs exchanged.
- (H.2): (F.2) and $0<c<\infty$. Both tails comparable, index $\beta$. This is the analogue of our (BAL), with $c$ playing the role of $p_-/p_+$.

The restriction $\alpha>\tfrac12$ comes from Erickson's strong renewal theorem, and the authors state the extension to $(0,1]$ as an open problem (p. 897). Doney's 1997 local condition removes that restriction in our setting.

## Results

- Theorem 2.1 under (H.1): $P(\sigma(t)>0)\to0$, with the rates $\alpha m_FV(t)/t\sim\alpha m_F/m_G(t)$ under (F.1), $\alpha B(\alpha,1-\beta)V(t)\bar F(t)$ under (F.2) with $\beta<1$, and $\alpha m_F(t)V(t)/t$ at $\beta=1$. Here $V$ is the renewal function of the delayed process and $m_G(t)=\int_0^t\bar G$. So the probability of being in the dominated state at time $t$ decays like $t^{\alpha-1}$ times a slowly varying factor when the dominated period has a finite mean, and like $\bar F(t)/\bar A(t)$ when it does not.
- Theorem 2.2 under (H.1): the conditional laws of $\sigma(t)$ given $\sigma(t)>0$, at the scale $1$ under (F.1) (limit $m_F(x)/m_F$), at the scale $t$ under (F.2) with $\beta<1$ (incomplete beta $B_x(\alpha,1-\beta)/B(\alpha,1-\beta)$), and through $m_F(\sigma(t))/m_F(t)$ at $\beta=1$ (uniform limit).
- Theorem 2.3 under (H.2): $P(\sigma(t)>0)\to1/(1+c)$, and the laws of $\sigma(t)/t$ on both sides, with incomplete beta functions in the parameters $(\beta,1-\beta)$. With $c=0$ this recovers Dynkin and Lamperti, and the $\beta=1$ case recovers Erickson.
- Section 4: three key renewal theorems for $\int_0^t\bar F(t-u)V(du)$ with a delayed renewal function $V$, the analogues of Erickson's Theorem 3 and of Anderson and Athreya, proved through a uniform local bound (Lemma 3.3) for $V$.

## Relation to Papers F and G

- G's related work said that they "study limit theorems for alternating renewal processes with infinite mean cycles, extending results of Dynkin, Lamperti and Erickson". This is correct but hides that the object is the current period, not the occupation time. F said "later refinements by Mitov and Yanev" of Lamperti's arcsine law, which is wrong: they do not refine the occupation law. Both sentences are corrected.
- Their (H.1) is the dominated regime at the level of the one-time marginal. Theorem 2.1 gives the decay of $P(\text{dominated state at }t)$, which is the derivative-level version of $E[A_N]/N\to0$. G's Theorem F describes the whole law of $A_N$ in the dominated regime, point by point, and credits the weak law to Darling and Kac, Cénac et al. and Yamato. We add one sentence crediting Mitov and Yanev for the marginal and its rate.
- Their $c$ is our balance ratio. Their $1/(1+c)$ is our $p_+$ when the plus side is the work period.
- Nothing in the paper concerns local limit theorems, the ends, the initial run beyond the delayed renewal function, aging, or the shape. The claim in G's introduction that we found no local limit theorem for the occupation count under infinite means and no treatment of the dominated regime at the local level stands.
