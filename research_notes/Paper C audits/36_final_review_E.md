# 36 final review E: sec_boundary.tex (Section 6)

Nothing was recomputed. Each change is listed as old, new, reason.

1. Setting, generalized kernel.
   Old: "holomorphic functions on a disc $|z|<2z_0$, for $\beta\in\mathcal K$. With"
   New: "... for $\beta\in\mathcal K$, with $z_0>0$ given there. With"
   Reason: $z_0$ was used before it is defined (it comes from Theorem L-facet).

2. Remark after Proposition layer-cubic.
   Old: "Let $G$ be the cycle of (e), with $q_{12}=\dots$" (the cycle in (e) has 2 states in $G$ and $i=3$)
   New: "Let $G$ be the 3-state cycle with the rates of (e), with $q_{12}=\dots$"
   Reason: the old wording pointed to a different $G$ than the one used in the example, which has 3 states in $G$ and 4 in $F$.

3. After Proposition layer-constants.
   Old: "in the visit fraction $\alpha_i$ the rate has"
   New: "in the occupation fraction $\alpha_i$ of $i$ the rate has"
   Reason: $\alpha_i$ is a time fraction, not a visit count (density versus count confusion).

4. Paragraph before Proposition layer-prefactor.
   Old: "the local law of $F$, which in occupation coordinates is $T^{-(k-1)/2}C_F(\alpha)e^{-TJ_F(\alpha)}$, have the same exponent"
   New: "the local law formula of $F$, ... (proved only on compact subsets of the open face), have the same exponent"
   Reason: the local law is not proved near the facet, so the comparison is of formulas.

5. Proof of Theorem layer (b),(c), Bessel facts.
   Old: "So $I_n\le I_1$ for all $\zeta>0$, and $|1-\cos nt-(1-\cos t)|\le n^2t^2/2$ and a Laplace estimate give"
   New: "Also $I_n\le I_1$ for $n\ge1$ and $\zeta>0$, since $I_n$ decreases in $n$. The bound $|1-\cos nt-(1-\cos t)|\le n^2t^2/2$ and a Laplace estimate give"
   Reason: the integral formula gives $I_n\le I_0$, not $I_n\le I_1$, so "So" did not follow. The monotonicity in $n$ is a standard fact and is now stated as such. Please check that the DLMF monotonicity in order is the citation you want.

6. Proof of Theorem layer (b), end of the case $1\le x\le\delta T$.
   Old: "Hence $\mathbf K_\beta=\mathbf B_\beta\exp(O(\sqrt{x/T}(1+x)))$, and with (a) this proves (b)."
   New: "Hence $\mathbf K_\beta/\mathbf B_\beta=e^{(\gamma_\beta-q_i)x}\mathcal A/\mathcal A_0=\exp(O(\sqrt{x/T}(1+x)))$, where the factor $e^{(\gamma_\beta-q_i)x}$ comes from $e^{-q_ix}$ in $\mathbf K_\beta$ against $e^{-\gamma_\beta x}$ in $\mathbf B_\beta$, and $\mathcal A_0$ is $\mathcal A$ with $\Xi=1$. With (a) this proves (b)."
   Reason: the displayed estimate of $\lambda(\rho_s)-\zeta$ is $-(\gamma_\beta-q_i)x+\dots$, and it only cancels against this factor. The factor was implicit (and is used explicitly in the proof of Proposition layer-cubic(b)).

7. Proof of Proposition layer-cubic(e).
   Old: "Since $\varkappa_\beta<0$, the proof of (d) shows that $\ell\ge\dots$"
   New: "Since $\varkappa_\beta<0$, (b) and the choice of $\delta_\beta$ as in the proof of (d) give $\ell\ge\dots$"
   Reason: (d) bounds $|\ell|$ only. The sign of $\ell$ (needed for "tends to infinity") comes from (b) and $\varkappa_\beta<0$.

8. End of Section 6, comments after Theorem layer-counts.
   Old: "For $k=2$, Theorem pair-counts gives the ratio in (a) exactly. By (b) ... since (a) then has an error of order one."
   New: "For $k=2$, Theorem pair-counts(a) gives the ratio $P_N(n)/P_{N'}(\hat n)$ exactly. By Theorem layer-counts(b) ... since Theorem layer-counts(a) then has an error of order one."
   Reason: "(a)" and "(b)" were ambiguous between the two count theorems.

Trims: none made. Every repeated passage found either carried a new hypothesis or served a different subsection.

Checked and left unchanged: ranges in Theorem layer (x <= delta T, S >= T/2, z_* <= z_0/2), the "x = o(T^{1/3})" claim after Theorem layer, the pair-face bound and its "attained" remark, the exponent comparison with the Bessel kernel asymptotic, the c_1 paragraph (reversible case only), and the dependence of each count statement on T <= eps_1 N^{1/2}. All \ifarxivbuild branches and \label commands are intact.
