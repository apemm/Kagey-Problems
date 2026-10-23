# Probability paper strengthening feasibility

*Research synthesis with completed C/F searches and verified D structural edits.*

**C warrants focused exposition without making submission depend on unproved uniqueness; F has a credible heavy-tail-only direction if its lattice local theorem becomes the contribution.** The proposed C score argument needs new estimates, although existing all-root localization substantially reduces the task. Its genericity statement needs corrected exceptions and a positive logarithmic time range; nested supports already have an exact reversible counterexample. For F, general slowly varying tails look feasible for each fixed finite-mean law, but the proposed logarithmic multiplier omits changes in normalization, amplitude and mean. The moving-exponent window remains conditional on uniform estimates. D has been shortened while preserving its detailed theorem statements and proof bodies. This report distinguishes those verified editorial changes from proposed C/F mathematics and does not certify whole manuscripts or predict acceptance.

## C already has a contribution beyond a generic path

C compares the largest **individual occupation-count atom** on every admissible exact support for the row-homogeneous family \(P_N=I+(T/N)Q\). At \(T=\tau\log N\), support selection minimizes \(\tau\lambda_F+|F|-1\); under irreducibility and positive starting mass on the face, explicit prefactors locate cross-face ties through logarithmic and constant orders. The useful distinction is the lattice penalty \(N^{-(|F|-1)}\), whole-face maximization, and comparison across different dimensions. The finite affine hull is an elementary consequence of these probability estimates, not a separate general spectral discovery. ([Current research and proof limits](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Probability paper strengthening feasibility/02_C_plan_and_literature.md>))

Earlier work already gives substantial pointwise information. Brydges–van der Hofstad–König, Theorem 2.1 and Proposition 3.1, treats densities for a specified exact range and endpoint, with pointwise bounds beyond exponential order. Hervé–Ledoux, Theorem 2.2 and Proposition 3.1, provides density local limits; its occupation application assumes irreducibility after deleting any one state. Their companion Theorem 6.1 supplies compact-family uniformity. Reopening the primary PDFs identifies the versions as **math/0611525v2, 1306.5353v1 and 1305.5644v2**, respectively; the first is the 2007 published-text reprint. C must explain its additional relative discrete approximation and global cross-support maximization. ([Brydges et al. v2](https://arxiv.org/pdf/math/0611525v2), [Hervé–Ledoux v1](https://arxiv.org/pdf/1306.5353v1), [companion v2](https://arxiv.org/pdf/1305.5644v2))

Benaïm–Bravo–Faure's 2026 vanishing-mutation paper, **v1**, §1.1 and Theorem 1, concerns typical occupation limits in a time-inhomogeneous trajectory; it does not establish C's finite-row maximizing atom. Existing metastable and freezing-chain results likewise require substantive comparison rather than dismissal as fixed-rate theory. The Sabot–Tarrès precise reversible-local-time lead cited by Hervé–Ledoux remains unresolved. Thus the targeted search found no matching assembled theorem, but supplies no priority guarantee. ([Benaïm et al., v1](https://arxiv.org/html/2602.06829v1), [Kim–Landim, v2](https://arxiv.org/html/2412.13515v2))

The focused EJP plan is sensible editorially: retain selection, sharp maxima/crossings, the complete-graph resolution and explicit constants; compress the cycle catalogue and duplicated examples. Keep a short reducible example to protect the prefactor's hypotheses. A generic-path corollary belongs beside the crossing theorem only after proof. The proposed acceptance percentages and two-week proof schedule have no evidential foundation. EJP's full-length scope supplies no verified 50-page ceiling or permission to hide essential proofs. Paper A is public, so dependency-by-dependency attribution is preferable to compulsory duplication: C already proves its multistate run count and main clipped-product comparison internally. ([EJP scope](https://imstat.org/journals-and-publications/electronic-journal-of-probability/), [Paper A, inspected record v3](https://arxiv.org/abs/2610.06935v3))

Moving near-vertex theory to a supplement is a thematic choice; material already incorporated from public B does not automatically become another publishable paper. The proposed arXiv packaging also needs testing: official TeX guidance warns that external-document links can fail when separately compiled PDFs are concatenated. Two main filenames in a README do not establish correct references, and the new-identifier strategy has not received policy clearance. ([Official arXiv TeX instructions](https://info.arxiv.org/help/submit_tex.html))

## C uniqueness needs score control on every active branch

Write \(D_N=\log M_F-\log M_G\), \(L=\log N\), \(\Delta=|F|-|G|>0\), and \(\delta=\lambda_G-\lambda_F>0\). The existing crossing theorem establishes existence and confines **every root in \([1,N^{1/3}]\)** within \(O(1/L)\) of the solution of
\[
\delta T+(\Delta/2)\log T=\Delta L-\log(K_F/K_G).
\]
Consequently, monotonicity on a deterministic neighborhood containing that cluster suffices for uniqueness on the full stated interval. Global monotonicity from \(T=1\) is unnecessary. ([Existing theorem and localization proof](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/paperC/sec_secondorder.tex:329>))

The plan's score must be corrected. With \(q_i=-Q_{ii}\), \(S\) switches and \(L_i\) staying transitions at state \(i\), exact differentiation gives
\[
\partial_T\log P_{N,T}(n)=\frac{\mathbb E[S\mid n]}T
-\frac1N\sum_i\frac{q_i\mathbb E[L_i\mid n]}{1-Tq_i/N}.
\]
Here \(L_i=n_i-m_i\), not the occupation count. Both the denominator and \(1/N\) matter. For the continuum run distribution the exact score is \(\mathbb E_w[M-1]/T-q\cdot\alpha\). The proposed proof must establish, uniformly near each face saddle,
\[
\partial_T\log f_T(\alpha)
=-I_F(\alpha)+\frac{|F|-1}{2T}+O(T^{-2}),
\]
and transfer it to discrete probabilities, with a sufficient target error \(O(T^2/N)\). Differentiate the exact torus integral, control its inserted phase and remainder, and compare switch-weighted discrete/continuum run sums using higher moments and clipping bounds. **An \(O(1/T)\) value remainder cannot simply be differentiated.** These estimates remain proof deliverables, not completed lemmas. ([Detailed derivation](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Probability paper strengthening feasibility/02_C_plan_and_literature.md>))

The estimate must hold for every active lattice maximizer. Each log maximum is a finite smooth envelope, locally Lipschitz and absolutely continuous; its right/left derivatives select the largest/smallest active slopes. Uniform score control then gives \(D_N'\ge\delta/2\) almost everywhere near the cluster. Together with all-root localization this would prove uniqueness. It proves a unique **support transition**, while occupation vectors on either support can remain tied.

Genericity also needs repair. In the positive-rate domain exclude equal exit rates for distinct same-size faces and triple ties among distinct cardinalities. The witness \(q_{ij}=a_j>0\) gives \(\lambda_F=\sum_{i\notin F}a_i\), showing that the required analytic equalities are nonidentities; distinct binary incidence vectors cannot be collinear. Their finite zero-set union is relatively closed and null. Excluding every triple-collinearity equation is wrong: singleton lines always meet at zero. No blanket \(K_F\ne K_G\) condition is needed; with uniform start all singleton constants are identically equal. Nongeneric chains remain covered by existing selection results, but coincident score lines and higher ties require separate resolution. ([Witness calculations](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Probability paper strengthening feasibility/02_C_plan_and_literature.md>), [Mityagin v1, Proposition 0](https://arxiv.org/pdf/1512.07276v1))

The **safe candidate**, conditional on the missing score proof and uniform exclusion estimates, fixes generic positive \(Q\), a full-support start, and \(0<a<b<\infty\): on \(T\in[a\log N,b\log N]\), hull supports occur in order, each adjacent pair changes once at the existing expansion, and both supports coexist at the crossing. An unqualified path starting at \(T=1\) is false: for rates \(q_{12}=1,q_{21}=2\), start \((1/10,9/10)\), the vertex ratio tends to \(9e^{-T}\), producing an earlier bounded-time exchange near \(\log9\).

Nestedness is definitively false within this framework. With uniform start, take
\[
Q=\frac1{40}\begin{pmatrix}-120&40&80\\40&-139&99\\80&99&-179\end{pmatrix}.
\]
The unique best singleton is \(\{1\}\), rate \(3\); the unique best pair is \(\{2,3\}\), rate \(29/20\); full support has rate zero. The other pairs are excluded by positive-definite differences whose scaled determinants are \(3422\) and \(1102\). Hence the hull path is \(\{1\}\to\{2,3\}\to\{1,2,3\}\), with breakpoints \(20/31,20/29\). This exact rational, symmetric, strictly positive-rate example replaces the proposed random search. ([Certificate](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Probability paper strengthening feasibility/02_C_plan_and_literature.md>))

## F can center a short paper on a fixed-law local theorem

Consider the alternating unit-speed lattice walk, with \(A_N\) counting positive steps. Its later runs are i.i.d. positive integers of maximal lattice span one, with survival \(\overline F(k)\sim k^{-\alpha}L(k)\), \(1<\alpha<2\), and \(\mu=\mathbb E\xi\). Define the inverse normalization by \(t\overline F(a(t))\to1\), rather than substituting a guessed slowly varying factor at \(t\). Set \(K_\alpha=-\Gamma(1-\alpha)\) and
\[
I_\alpha=\frac{\Gamma(1+1/\alpha)}
{\pi[2K_\alpha|\cos(\pi\alpha/2)|]^{1/\alpha}}.
\]
The **candidate fixed-law theorem**, with fair initial direction and any independent almost surely finite first run \(D\), is, along even \(N\),
\[
C_N:=\Pr(A_N=N/2)\sim\frac{2I_\alpha}{a(N/(2\mu))}.
\]
Here \(D\) is independent of the direction and later runs; no finite mean of \(D\) is required. For the stationary residual start, one endpoint has mass \(E_N\sim N^{1-\alpha}L(N)/[2(\alpha-1)\mu]\), so
\[
R_N:=E_N/C_N\sim
\frac{N^{1-\alpha}L(N)a(N/(2\mu))}
{4(\alpha-1)\mu I_\alpha}.
\]
For a fresh start, \(R_N\sim\overline F(N)a(N/(2\mu))/(4I_\alpha)\). These conventions distinguish one endpoint from both, run survival from residual survival, and the mesh-two displacement from mesh-one occupation count. ([Derivation and normalization](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Probability paper strengthening feasibility/01_F_novelty_and_math.md>))

The research notes provide a detailed route through the exact two-renewal identity, but formal write-up and an independent line-by-line check remain. The important improvement is that tail regular variation need not imply regular variation of individual masses. Caravenna–Doney **v3**, Theorem 1.1, Eq. (1.6), gives the weaker local deviation bound needed in the early-index region. With \(h=N/2\), its contribution after rescaling is bounded by \(C[a(h)+h]\overline F(h)\to0\). This avoids a stronger point-mass assumption for \(\alpha>1\). Berger **v4**, Theorem 2.4—not the old notes' Theorem 2.7—provides a conservative alternative under a local-mass bound. ([Caravenna–Doney v3](https://arxiv.org/pdf/1612.07635v3), [Berger v4](https://arxiv.org/pdf/1706.07924v4))

For \(\overline F(k)\sim A k^{-\alpha}(\log k)^\beta\), \(\beta\in\mathbb R\), inverse normalization yields
\[
a(t)\sim A^{1/\alpha}\alpha^{-\beta/\alpha}
t^{1/\alpha}(\log t)^{\beta/\alpha}.
\]
Writing \(\phi=(1+\sqrt5)/2\) and \(C_{\rm pure}(\phi)\) for the current exact pure-power ratio constant,
\[
R_N\sim C_{\rm pure}(\phi)A^\phi\phi^{-\beta/\phi}
\left[\frac{\zeta(\phi)}\mu\right]^\phi(\log N)^{\beta\phi}.
\]
**The proposed exponent \(\beta\phi\) is correct; the unchanged constant is generally wrong.** Finite changes to the run-law body change \(\mu\) without changing its tail. Thus positive/negative \(\beta\) decides endpoint/center dominance, while \(\beta=0\) requires the full constant. For unrestricted \(L\), retain the inverse formula: the critical factor can grow, vanish or oscillate, and is not universally \(L(N)^\phi\).

## F's local upgrade must earn its novelty and moving window

The golden-ratio balance is already explicit in Wang–Li–Hänggi's author-hosted chapter, §6.2.1.3, Eq. (6.49), pp. 267–268. Godrèche–Luck **v1**, §7, Eqs. (7.12)–(7.15), already gives the stable bulk coefficient; a mesh-two adjustment reproduces F's pure-power central constant. Cénac et al. **v1**, Theorems 3.2–3.3, already covers general stable attraction and slowly varying functional scaling. The potential increment is a rigorous **individual lattice probability** theorem with arbitrary finite initial delay and exact persistence comparison. Distributional convergence alone supplies no such local conclusion. ([Wang–Li–Hänggi chapter](https://www.physik.uni-augsburg.de/theo1/hanggi/Papers/678.pdf), [Godrèche–Luck v1](https://arxiv.org/pdf/cond-mat/0010428v1), [Cénac et al. v1](https://arxiv.org/pdf/1612.00238v1))

Akimoto **v1**, §V, is a close ordinary/equilibrium/aging occupation comparator. Directionally reinforced walks and regenerative/semi-Markov local theorems remain unresolved overlap risks, particularly their handling of an unfinished cycle. The research did not locate a matching theorem, but did not complete those checks. Dropping the aging half improves focus: DLS **v1**, Theorem 2.18, already implies its count marginal, and the March 18, 2024 Engländer–Volkov author draft supplies further urn/joint-law precedents; published-book numbering remains unverified. ([Akimoto v1](https://arxiv.org/html/2306.00359v1), [DLS v1](https://arxiv.org/pdf/1901.08135v1), [dated author draft](https://www.researchgate.net/publication/379333206_Coin-Turning_Random_Walks_and_Inhomogeneous_Markov_Chains))

For the exact pure-power family, a **uniform** center theorem near \(\phi\) would imply, with \(d=1+\phi^{-2}\),
\[
\alpha_N=\phi-\kappa/\log N
\quad\Longrightarrow\quad
R_N\to C_{\rm pure}(\phi)e^{d\kappa}.
\]
The predicted tie is \(\kappa_*=0.1833858634\ldots\), using \(C_{\rm pure}(\phi)=0.7761317206\ldots\). Substitution into a pointwise theorem does not prove it. The missing uniform Fourier/LLT bounds, delayed-kernel truncations, outer-region estimates and stationary-delay tightness are substantive deliverables. Continuity and a uniform limit give a crossing's existence and leading location in the shrinking bracket, **not uniqueness**. A logarithmic tail changes the center by order \(\log\log N/\log N\); arbitrary varying slowly varying families need separate assumptions. ([Conditional window and proof program](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Probability paper strengthening feasibility/01_F_novelty_and_math.md>))

More precisely, if \(D_\phi=C_{\rm pure}(\phi)A^\phi\phi^{-\beta/\phi}[\zeta(\phi)/\mu_\phi]^\phi\) and the logarithmic family has suitable uniformity and a continuous body law, its predicted crossing is
\[
\alpha_N=\phi+
\frac{\beta\phi\log\log N+\log D_\phi}{d\log N}
+o(1/\log N).
\]
This remains conditional. Specify logarithmic survival tails only beyond a cutoff, with valid probabilities below it; those choices determine \(\mu_\phi\).

Retain the existing pure-law local Lamperti theorem for \(0<\alpha<1\), but do not advertise an all-\(L\) extension: its early-index argument needs different control. Keep \(\alpha=1\) outside the theorem, and demote \(\alpha\ge2\) comparisons; general tails at two need truncated-variance norming, not automatically \(\sqrt{N\log N}\). A plausible editorial budget is **12–15 pages**, or **14–17** with the uniform window, including references. These are estimates, not builds or a journal verdict.

## D needs measured deletion alongside relocated technical proofs

D's earlier review identifies the same count chain and a Landau approximation in Bokes–Hlubinová–Singh; its publication case rests on rigorous uniform errors and the logarithmic crossing comparison. The substantive shortening direction is therefore to retain the center comparison and compound-Poisson/Landau analytic argument, compress repeated heuristic/proof previews, keep technical statement blocks readable, and relocate supporting technical proofs and verification inventories where dependencies allow. This is an editorial proposal based on the existing review, **not fresh completed D research**. ([Earlier synthesis](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/reports/Final probability papers review.md>), [published predecessor, Eqs. (6)–(10), (58)–(60)](https://mdpi-res.com/d_attachment/axioms/axioms-12-00249/article_deploy/axioms-12-00249.pdf))

The parent's structural edit retains five family-estimate statements in main and preserves their proof bodies verbatim in [or_family_proofs.tex](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/paperD/or_family_proofs.tex>); the full [app_erw_signs.tex](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/paperD/app_erw_signs.tex>) proof file is included by Online Resource §S5 instead of main. The core center and compound-Poisson/Landau proofs stay in the article. Sections 2–3 retain their exact finite-\(N\) statements; introductory summaries in §§1.2–1.3 are rewritten. These are parent-reported preservation facts, not an independent proof re-audit here.

Actual deletion targets repeated prior-work descriptions, introductory headline bounds restated in theorem sections, and verification metadata already documented in the code/coverage records. The editorial direction is to retain the assumptions, error ranges and proof-dependency links needed to assess each theorem. This improves the paper's argument as well as its length; moving indispensable reasoning without a readable bridge would not.

The measured baseline is **41 main + 12 Online Resource = 53 combined pages**. The first structural build was **36 + 17 = 53**. After deleting redundant introduction/prior-work/verification prose, the final verified build measures **35 main + 17 Online Resource = 52 combined pages**: **six fewer main pages, one fewer page overall**. Most main-text shortening is relocation. The final sign-pattern wording specifies deleting zeros **and merging equal neighbours**. All three PDFs compile without undefined or duplicate labels. Automated source comparisons confirm identical moved proof bodies, unchanged detailed statement blocks, and byte-identical center and bulk proof files. No slow sweeps or Lean runs were performed. This source-preservation check is not a fresh proof audit or D literature investigation.

**Next priorities:** finish C's active-branch score estimates before claiming uniqueness, and independently check F's tail-only local proof and regenerative-theorem overlap before rewriting. These checks determine which stronger claims the evidence supports.
