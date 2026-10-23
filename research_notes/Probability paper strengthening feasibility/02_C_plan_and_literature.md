# Paper C: audit of the proposed EJP plan and strengthening feasibility

Research notes, 22 October 2026 (Los Angeles). Initial time-bounded pass; research only. No manuscript edits, commits, Lake runs, random searches, or numerical sweeps. The requested `researcher.md` was the first file read. The proposal audited is [the new focused plan](<C:/Users/arjun/Downloads/Paper C for EJP focused plan, new results and what to keep.md>). Source labels below are more durable than printed theorem numbers. Local evidence is a research aid, not a public full-text redistribution.

## 1. Do Goals 1–3 actually imply the proposed generic complete mode path?

### Takeaway

**The promising target is a unique support transition at each positive logarithmic hull breakpoint. The proposed derivative argument is not yet a proof, but the existing all-root localization means that a derivative estimate only near the crossing can yield uniqueness on the entire stated interval.** The proposed unrestricted “complete path as T grows” needs a starting-range qualification for a nonuniform start. The genericity argument can be repaired without imposing inequalities between K constants. Nestedness fails even for three states, symmetric rates, and strictly positive off-diagonal entries; an exact rational certificate is below. These conclusions use the current [first-order source](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:385>), [crossing source](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:329>), and direct derivations in this section.

### Cited Findings

#### 1.1 What the current crossing theorem already establishes

Let L=log N, Δ=k_F−k_G≥1, δ=λ_G−λ_F>0, with both faces satisfying (H). Theorem `thm:crossing`, currently Theorem 4.7, proves existence and **localizes every root in [1,N^(1/3)]**, not just roots initially assumed to lie in a tie window. Specifically,

\[
D_N(T)=-\Delta L+\delta T+\frac\Delta2\log T+
\log(K_F/K_G)+O(T^{-1}+T^2/N).
\]

The error is bounded throughout that interval. At any root, comparison with the increasing function Ξ(T)=δT+(Δ/2)log T first gives T comparable to L; substitution then improves the error to O(1/L). If T° solves Ξ(T°)=ΔL−log(K_F/K_G), every root satisfies |T−T°|≤C/L. This is explicitly proved in parts (ii)–(iii), including the rough-localization step. [Current proof, `thm:crossing`](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:351>).

**Consequence, established by this comparison:** prove strict monotonicity of D_N only on a deterministic interval containing that O(1/L) root cluster, or on a convenient surrounding interval [cL,CL]. Existence plus all-root confinement plus monotonicity there gives exactly one root in **all of [1,N^(1/3)]**. There is no need to prove global monotonicity from T=1. Conversely, a window argument without the current all-root confinement would prove only window uniqueness. [The same theorem, parts (i)–(iii)](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:329>).

The plan should therefore separate two statements: a local derivative lemma and the full-interval uniqueness corollary that uses existing localization. Calling the former alone a proof of the latter obscures an essential logical step. This is an inference from the cited proof, not a new imported theorem.

#### 1.2 The exact discrete score: the plan omits a denominator and a factor

For a path x=(x₁,…,x_N), let S be its number of switches, and let L_i be the number of **staying transitions** i→i. There are N−1 transitions; L_i is not the occupation count n_i. At fixed N and fixed composition n, differentiating each path weight gives the exact identity

\[
\boxed{\partial_T\log P_{N,T}(n)
=\frac{\mathbb E_{N,T}[S\mid n]}T
-\frac1N\sum_i\frac{q_i\,\mathbb E_{N,T}[L_i\mid n]}{1-Tq_i/N}.}
\tag{S1}
\]

Indeed a switch contributes log(T/N)+log q_ij, and a stay contributes log(1−Tq_i/N). Summing derivatives and normalizing the positive finite sum yields (S1). In run notation L_i=n_i−m_i and S=∑m_i−1. Thus the second term is approximately −q·α, but it is **not exactly** minus an unscaled sum of diagonal rates. The proof uses only the path law and the already self-contained run expansion. [Model and `lem:runs`](<../../kagey-problems/problem131/paperC/sec_model.tex:168>).

At fixed α in the open face, give continuum run vectors m their normalized weights proportional to

\[
W(m)\prod_i (T\alpha_i)^{m_i-1}/(m_i-1)!.
\]

The formula f_T(α)=T^(k−1)e^(−Tq·α)H(Tα) then gives another **exact** score identity:

\[
\boxed{\partial_T\log f_T(\alpha)
=\frac{\mathbb E_w[M-1]}T-q\cdot\alpha,\quad M=\sum_i m_i.}
\tag{S2}
\]

The power T^(k−1) together with the M−k powers in H produces M−1, so no unexplained extra k−1 remains. Conditioning on α in (S2) means this density-based run distribution, not conditioning on a positive-probability point event in continuous time. [Continuum law, `lem:continuum`](<../../kagey-problems/problem131/paperC/sec_model.tex:211>); [definition of w in discrete-comparison proof](<../../kagey-problems/problem131/paperC/app_torus.tex:411>).

#### 1.3 What must be proved for the derivative route

The desired continuum estimate is

\[
\partial_T\log f_T(\alpha)
=-I_F(\alpha)+\frac{k-1}{2T}+O_{\mathcal K}(T^{-2})
\tag{S3, proposed lemma}
\]

uniformly on a fixed compact neighborhood of α*_F. The current value expansion alone does not prove (S3). For example, R(T)=T^(−1)sin(T³) is uniformly O(1/T), while R′(T)=−T^(−2)sin(T³)+3T cos(T³) is large. Even a smooth, uniformly small error is insufficient. [Existing `thm:local`](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:181>).

The Laplace lemma with a parameter currently assumes a **compact metric** parameter space and controls derivatives in the torus variable; it does not claim differentiation of its remainder in an external parameter. Its name is not evidence of a C¹ asymptotic theorem. [Exact assumptions of `lem:laplace`](<../../kagey-problems/problem131/paperC/app_laplace.tex:10>).

A more concrete proof route than “carry one more variable” is available. In the exact torus integral, differentiate under the integral in T, producing an amplitude containing the phase Ψ. After removing e^(TΨ(0)), expand the numerator with insertion Ψ−Ψ(0) and the original denominator together. The Gaussian quadratic insertion supplies −(k−1)/(2T) for the integral; the outside factor T^(k−1) supplies +(k−1)/T. Their sum gives +(k−1)/(2T). Odd-term cancellation and one further controlled remainder are needed for O(T^(−2)) after taking the ratio. Compactness, a nonzero leading amplitude, and the off-saddle exponential bound must survive the insertion. This is a **proof blueprint**, not a claim that I completed its uniform remainder audit. [Torus representation and local-law proof](<../../kagey-problems/problem131/paperC/app_torus.tex:145>); [Laplace proof](<../../kagey-problems/problem131/paperC/app_laplace.tex:10>).

The existing comparison of discrete and continuum run weights is useful but also needs strengthening. It has P/(N^(−(k−1))f)=E_w κ_m and

\[
(1-M^2/(2n_{\min}))e^{-q_{\max}^2T^2/N}\le\kappa_m
\le e^{hq_{\max}M}.
\]

It proves E_w M²=O(T²) using a Chernoff bound from log E_w e^(M−1)≤CT. The same tail argument should give each fixed higher moment. To transfer the **score**, control E_w[Sκ_m]/E_w κ_m, not merely E_w κ_m. A third-moment estimate and exponentially weighted moments should yield the conservative bound

\[
\mathbb E_{N,T}[S\mid n]-\mathbb E_w[S]=O(T^3/N),
\quad
\partial_T\log P_{N,T}(n)-\partial_T\log f_T(\alpha)=O(T^2/N).
\tag{S4, target bounds}
\]

The stay correction in (S1) is only O(T/N) if E[M]=O(T); the switch comparison is the larger conservative error. These bounds require a written treatment of the clipped terms m_i>n_i and exponential weights. They are not obtained by differentiating the current O(T²/N) value estimate. On T comparable to log N, even these coarse target errors are ample. [Exact κ bounds and moment proof, `eq:A-kappa`, Steps 1–4](<../../kagey-problems/problem131/paperC/app_torus.tex:411>).

At **every active face maximizer**, `thm:facemax` gives α−α*=O(1/T). Since I is analytic, ∇I(α*)=0, and its Hessian is positive definite, I(α)−λ_F=O(T^(−2)). Thus (S3)–(S4), if established, imply for every active composition

\[
\partial_T\log P_{N,T}(n)
=-\lambda_F+\frac{k_F-1}{2T}
+O(T^{-2}+T^2/N).
\tag{S5, conditional deduction}
\]

For T comparable to L this gives the proposed δ+Δ/(2T)+o(1) difference. The Perron identity explains the leading cancellation but does not itself establish the order-one correction to the conditional expected switch count. In fact that expected count must have the precision

\[
\mathbb E_w S=T(q\cdot\alpha-I_F(\alpha))+(k-1)/2+O(1/T)
\]

to yield (S3). A law of large numbers alone is insufficient. For uniqueness alone, an o(1) error in the score, without identifying the 1/T coefficient, would suffice. [Maximizer localization](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:307>); [rate Hessian and constants](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:78>).

#### 1.4 Maxima may switch: the correct envelope argument

For fixed N, log M_F is the maximum of finitely many smooth log probabilities. It is locally Lipschitz and absolutely continuous. If A_F(T) is its set of active compositions, elementary finite-envelope calculus gives

\[
(\log M_F)'_+(T)=\max_{n\in A_F(T)}(\log P_n)'(T),\qquad
(\log M_F)'_-(T)=\min_{n\in A_F(T)}(\log P_n)'(T).
\]

To verify: inactive branches remain inactive in a sufficiently small neighborhood, and the first-order expansions of the active branches select the largest slope to the right and the smallest to the left. This is a direct derivation from the finite polynomial representation used in the current crossing proof. [Continuity/finite-maximum argument](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:357>).

Apply a uniform estimate such as (S5) to **all** active branches of both faces. Then both one-sided derivatives of D_N are δ+Δ/(2T)+o(1), or equivalently its almost-everywhere derivative is ≥δ/2 in the root-containing interval. Absolute continuity implies D_N(b)−D_N(a)≥(δ/2)(b−a). One must not apply an envelope theorem as if there were a single smoothly moving maximizer; lattice maximizers may exchange. At the unique crossing both supports carry global modes if all other faces have been excluded. The assertion is uniqueness of the support transition, not uniqueness of the occupation vector on either support. [Face maximum definition](<../../kagey-problems/problem131/paperC/sec_model.tex:48>); [tie-window exclusion](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:391>).

#### 1.5 A workable closed-null genericity argument, without K inequalities

Work in the connected open positive-rate domain Ω=(0,∞)^(d(d−1)), with Q_ii=−∑_{j≠i}q_ij. Every nonempty face is irreducible and, for fixed full-support μ, satisfies (H). Each λ_F is real analytic in Ω because its Perron eigenvalue is simple; the local eigenvalue argument already used in C applies to these rate parameters. “Closed” below means **relatively closed in Ω**. It does not include uniform estimates as rates approach the boundary. [Perron simplicity and model](<../../kagey-problems/problem131/paperC/sec_model.tex:40>); [analytic perturbation argument](<../../kagey-problems/problem131/paperC/app_torus.tex:44>).

Here is an explicit nonidentity witness that the plan currently lacks. Set q_ij=a_j for i≠j, with every a_j>0 and s=∑a_j. Then

\[
Q=\mathbf1a^\top-sI,\qquad
\lambda_F=s-\sum_{i\in F}a_i.
\tag{G1}
\]

The submatrix on F has positive eigenvector 1 and eigenvalue ∑_F a_i−s, hence this is its Perron eigenvalue. Thus, for distinct **same-size** F,G, λ_F−λ_G is not identically zero: on (G1) it is the nonzero linear form ∑_G a_i−∑_F a_i. This removes coincident first-order lines of equal intercept. This witness is an elementary calculation from C's definition of λ_F, not an attributed external result. [Definition of exit rate](<../../kagey-problems/problem131/paperC/sec_model.tex:48>).

After excluding those pair equalities, three active faces at a positive breakpoint must have pairwise different sizes. Put y_F=|F|−1 and exclude zeros of

\[
A_{FGH}=(y_G-y_H)\lambda_F+(y_H-y_F)\lambda_G
+(y_F-y_G)\lambda_H.
\tag{G2}
\]

On (G1), (G2) is a linear form whose coefficients are a nontrivial affine combination of the three distinct incidence vectors 1_F,1_G,1_H. Three distinct vertices of a binary cube cannot be collinear: a proper convex combination of two different binary vectors has a coordinate strictly between 0 and 1. Since the y values differ, vanishing of that coefficient vector would assert precisely such collinearity. Therefore (G2) is not an analytic identity either. This supplies a witness **for every required triple**, rather than one informal perturbation for an unspecified example. [Hull tie condition in `thm:hull`](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:491>).

A nonzero real-analytic function on a connected open domain has a null zero set. Finite unions of these pair/triple zero sets are relatively closed and Lebesgue null. Outside their union there is a unique winning face between positive breakpoints and precisely two at each breakpoint. This finite genericity conclusion follows from the explicit witnesses above and [Mityagin, Proposition 0, PDF p. 1](https://arxiv.org/pdf/1512.07276). The source's abstract and proposition locator were checked; no independent audit of its proof is claimed.

**Structural trap:** all singleton lines Φ_τ({i})=τq_i meet at τ=0 for every Q, and their hull points all have intercept zero. The all-singleton “three points are collinear” equation is identically zero. More generally every fixed cardinality lies on a horizontal line in (λ,k−1) space. Excluding all triple-collinearity equations would exclude the entire parameter space. The corrected construction handles equal cardinality by pairwise eigenvalue inequalities and applies (G2) only to distinct cardinalities and positive breakpoints. [Affine scores and hull statement](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:479>).

**No K_F≠K_G condition is needed for two generic hull neighbors.** Different sizes and a positive breakpoint imply δ=Δ/τ*>0. The crossing is transverse independently of whether K_F=K_G; equality simply changes the constant shift. Equal-size, equal-λ faces are already excluded. Moreover K_singleton=μ_i, so with a uniform start all singleton K's are identically equal as functions of the rates. A blanket “K equalities form a null set” claim is false in that setting. If a different theorem retains equal-size eigenvalue degeneracies, specify exactly which coincident score lines require a finer comparison. [K definition](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:45>); [crossing hypotheses](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:329>).

#### 1.6 The proposed “complete path” needs an explicit T range

Theorem `thm:first` is stated at **fixed τ>0**. It does not by itself cover T bounded while N grows or all T beyond the slowly switching range. A nonuniform start produces a concrete obstruction to starting the hull path at T=1. Take d=2, q₁₂=1, q₂₁=2, μ=(1/10,9/10). The first hull winner for every sufficiently small fixed positive τ is {1}, since q₁<q₂. But

\[
\frac{M_{\{2\}}(T)}{M_{\{1\}}(T)}
=9\left(\frac{1-2T/N}{1-T/N}\right)^{N-1}
\longrightarrow9e^{-T}.
\]

At T=1 state 2 wins, and the vertices exchange dominance near T=log 9, before the logarithmic transition to the full face. On bounded T intervals the two-state full-face maximum is O(1/N), whereas the vertex masses stay positive, so this is a genuine global-mode effect for large N. The strict inequalities persist on an open set of rates; deleting a rate-null exception cannot remove the obstruction. [Exact singleton formula](<../../kagey-problems/problem131/paperC/sec_model.tex:205>); [bounded-T face maximum bound](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:293>).

**Safe proposed statement, conditional on Goal 1:** fix Q outside the exceptional set, full-support μ, and 0<a<b<∞ containing the desired hull breakpoints. For all sufficiently large N, on T∈[aL,bL], the mode supports follow the hull faces in order; each consecutive pair crosses exactly once, all other faces are strictly smaller there, and the transition locations satisfy the current crossing expansion. Explain the set of two supports at the transition. A claim covering [T₀(Q,μ),N^(1/3)] may also be feasible, but needs separate early/late exclusion estimates. An unqualified claim for every T allowed by stochasticity is much larger than the current theory. [Fixed-τ selection](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:402>); [uniform window exclusion](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:391>).

Uniformly filling gaps between finitely many windows requires a compact positive score gap and the uniform value estimates, not merely pointwise invocation of `thm:first` for each τ. Pairwise equality of two nonwinning faces is not a global support change. At most d−1 positive hull transitions occur because winning cardinalities strictly increase. [Hull ordering](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:491>).

#### 1.7 Exact rational reversible counterexample to nestedness

Take uniform μ and the symmetric generator

\[
Q=\frac1{40}\begin{pmatrix}
-120&40&80\\40&-139&99\\80&99&-179
\end{pmatrix}.
\tag{N1}
\]

Every off-diagonal rate is positive. The singleton exit rates are 3,139/40,179/40, so {1} uniquely wins among singletons. On {2,3}, −40Q_F has eigenvalues 58 and 260: its trace is 318, and (139−58)(179−58)−99²=81·121−9801=0. A positive eigenvector for eigenvalue 58 is (11,9). Therefore λ_{23}=58/40=29/20. To show this is the unique least pair exit rate, subtract (29/20)I from the other two pair matrices −Q_F. In units of 1/40, their first diagonal entry is 62 and determinants are

\[
62\cdot81-40^2=3422>0,\qquad
62\cdot121-80^2=1102>0.
\]

Both matrices are positive definite by the two-by-two criterion, so their least eigenvalues exceed 29/20. Full support has λ=0. These exact identities certify all competing faces; there is no simulation or floating-point inference. [Exit-rate definition](<../../kagey-problems/problem131/paperC/sec_model.tex:48>).

The three relevant affine scores are 3τ, 1+(29/20)τ, and 2. Their lower envelope is

\[
\{1\}\quad(0<\tau<20/31),\qquad
\{2,3\}\quad(20/31<\tau<20/29),\qquad
\{1,2,3\}\quad(\tau>20/29).
\tag{N2}
\]

The intervals are nonempty because 20/31<20/29. At the first transition the supports are disjoint. By C's existing selection theorem these are also the unique eventual global-mode supports at fixed τ in the respective open intervals. Thus **nestedness is false even for reversible, all-positive generators**; no d=4,5,6 search is needed. Strict face and hull gaps make the phenomenon stable under small perturbations. Rayleigh monotonicity for F⊂G compares those particular sets, and cannot force independently optimal sets at different sizes to be nested. [Selection and hull theorems](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:385>).

This is the single bounded exact toy certificate in this pass. Its determinant products, trace, and positive eigenvector equation were independently checked with integer BigInt arithmetic: 0, 3422, 1102, trace 318, and two zero eigenvector residuals. No numerical sweep was used. The current paper already says a winner can move to a disjoint community near the end of `sec_firstorder`; the new value here is an explicit minimal symmetric certificate, not a claim that nonnestedness was absent from C. [Existing disjoint-community sentence](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:579>).

### Inferences

- **Priority:** first prove the score estimate only on T comparable to log N, with all active maximizers included; then use the already-proved root confinement. This avoids spending the research budget on unnecessary T=1 derivative asymptotics. The derivative insertion and weighted discrete moment comparison are the substantive work. The plan's two-week estimate is unsupported, and the follow-on generic theorem still needs careful uniform patching. [Existing proof infrastructure](<../../kagey-problems/problem131/paperC/app_torus.tex:401>).
- A reversible-only crossing result would be a legitimate intermediate result, but reversibility does not repair the initial-T or envelope issues. The nonnested certificate already resolves Goal 3 analytically. [N1–N2 above; symmetric-face rate formulation](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:579>).

### Gaps

- I have not completed a rigorous uniform proof of (S3)–(S5), including insertion remainders and weighted clipping estimates. Consequently **Goal 1 and the new path theorem remain proposals**, even though the exact score identities, genericity witness, initial-range obstruction, and rational nonnested example are derived above.
- This is not a re-audit of every existing proof or imported complete-graph result. The prior mathematical review's explicit exclusions remain relevant. [Prior audit coverage](<../Final probability papers review/01_C_mathematical_referee.md>).

## 2. What do the nearest primary sources say, and what novelty survives without new research?

### Takeaway

The strongest existing claim remains a **global comparison of discrete occupation-count maxima across exact supports of different dimensions**, including arbitrary-start first order and explicit prefactors under (H). A generic one-transition theorem would sharpen temporal behavior, but is not needed to explain that contribution. The fresh search found a relevant 2026 vanishing-mutation occupation paper and an additional pointwise-large-deviation lead; neither establishes a prior theorem identical to C in the inspected material. This is bounded search evidence, not priority clearance. [C main introductory claims](<../../kagey-problems/problem131/paperC/sec_intro.tex:53>).

### Cited Findings

#### 2.1 Closest local-time and modal precedents, with reading limits

| Primary source | Verified locator and result | Consequence for C / access limit |
|---|---|---|
| Hervé–Ledoux, *Local limit theorem for densities of the additive component of a finite Markov Additive Process* | Theorem 2.2; Remark 2.3; Proposition 3.1 and Remark 3.1, PDF pp. 3–6. Density Gaussian approximation; local-time application assumes irreducibility of G and every one-state-deleted subgenerator. | Do not claim predecessors only bound neighborhoods, or lack parameter uniformity. Freshly reopened and inspected these statements; did not reread the entire Fourier proof. [Primary PDF](https://arxiv.org/pdf/1306.5353). |
| Hervé–Ledoux, *Additional material…* | §5.1, Proposition 5.1; §6, Theorem 6.1, PDF p. 15, assumptions U1–U3. Explicit compact-family uniform LLT. | This companion is a closer methodological comparator than a vague “fixed generator” contrast. C still needs relative sharp estimates, discrete comparison and whole-face maximum exclusion. Fresh access to the full PDF achieved; reading targeted at these statements. [Primary PDF](https://arxiv.org/pdf/1305.5644). |
| Brydges–van der Hofstad–König, *Joint density for the local times of continuous-time Markov chains* | Theorem 2.1, (2.4)–(2.5), PDF p. 4: exact density for specified range R and endpoint b. Proposition 3.1, (3.1), PDF p. 14: pointwise density bound beyond exponential order. | Exact support/range and pointwise control are already prior art. C's comparison of lattice atoms with different cell dimensions is the useful distinction. Fresh full-PDF access; targeted statements read, not full proof certification. [Primary PDF](https://arxiv.org/pdf/math/0611525). |
| Dekking–Kong, *Multimodality of the Markov binomial distribution* | Proposition 4.3 and Theorem 4.1, as documented in the prior targeted reading: interior log-concavity and classification of modal shapes. | Genuine two-state modal precedent. Different from multistate support optimization, but do not imply that studying occupation modes itself is new. Locators inherited from prior notes/local evidence; not newly audited here. [Primary PDF](https://arxiv.org/pdf/1102.3613); [prior comparison](<../Final probability papers review/02_C_literature_and_EJP.md>). |

**New pointwise lead:** Hervé–Ledoux, PDF pp. 2 and 13, mentions precise reversible local-time asymptotics and lists Sabot–Tarrès, *Vertex reinforced jump process and large deviation of reversible Markov jump processes*, “In preparation, 2013.” I did not resolve this to an accessible completed theorem. It remains a literature gap, not a verified predecessor. [Introduction and bibliography](https://arxiv.org/pdf/1306.5353).

For all-positive faces, C's tilted generator also has all positive off-diagonal entries, so its one-state-deleted subgenerators meet the extra irreducibility condition automatically (with singleton deletions interpreted trivially). Thus the new generic theorem's restricted setting is particularly close to the earlier LLT machinery. The existing arbitrary irreducible-face treatment has broader graph scope. This is a direct hypothesis comparison, not a claim that their theorem automatically yields C's sharp error. [C tilted-generator definition](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:28>); [Hervé–Ledoux Proposition 3.1](https://arxiv.org/pdf/1306.5353).

#### 2.2 Fresh vanishing-mutation result

Michel Benaïm, Mario Bravo and Mathieu Faure, *On the occupation measure of evolution models with vanishing mutations*, arXiv:2602.06829, is a relevant new comparison. I opened the **version-pinned v1 full HTML**, read §1.1 and the main Theorem 1 statement in §2, rather than relying on a search abstract. Under its admissibility and A-vanishing assumptions with 2A e(c)<1, Theorem 1(a) proves almost-sure convergence of the empirical occupation measure to π*. The model is time-inhomogeneous, with mutation declining along one trajectory. This concerns typical occupation limits and stochastic selection, not the maximizing individual finite-length count atom across faces. Later-version metadata surfaced in search, but its numbering/proofs were not checked; the locator here is v1 only. [Primary v1 full text, §1.1 and Theorem 1](https://arxiv.org/html/2602.06829v1); [authors' institutional working-paper listing](https://www.amse-aixmarseille.fr/fr/recherche/documents-de-travail?bibcite_year=2026&field_wp_annee_value=5&page=1).

This suggests a precise extra comparison if needed: distinguish **a support selected by the typical long-time occupation law** from **the support of the single most probable lattice composition**. The former can be full support while the latter is a vertex. C already demonstrates that distinction on the 4-cycle. [Worked example, final comparison](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:136>).

#### 2.3 Existing small-noise/metastable literature must not be caricatured

The previous literature audit records the following primary-source locators: Dietz–Sethuraman, Theorems 1.3–1.5, for time-inhomogeneous occupation laws; Bouguet–Cloez, Theorem 2.9, for freezing chains; Kim–Landim, Theorem 2.3 in arXiv v2, for Gamma-convergence of rescaled measure-flow rate functions. These provide substantive varying-rate precedents, but not an all-support atom-maximization statement in the inspected results. I rely on that prior targeted source reading here, rather than claim a fresh proof-level reading of all three. [Dietz–Sethuraman](https://arxiv.org/pdf/math/0701798); [Bouguet–Cloez](https://arxiv.org/pdf/1705.02121); [Kim–Landim, version-pinned text](https://arxiv.org/html/2412.13515v2); [prior audit](<../Final probability papers review/02_C_literature_and_EJP.md>).

Searches also covered principal-submatrix eigenvalue optimization, optimal Dirichlet subsets/cardinality, low mutation, small noise, occupation modes and support selection. Nearby results about graph partitions or stationary stochastic stability were not close enough to justify importing theorem claims. **The finite affine hull is an elementary consequence once the probabilistic maximum estimates are known.** It should not be sold as a new general eigenvalue-hull principle. [C's direct finite-envelope proof](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:518>).

### Inferences

The strongest novelty statement available **without Goals 1–2** is already substantial and narrow:

> For the row-homogeneous family P_N=I+(T/N)Q, with fixed finite Q and start, compare the largest individual occupation-count probabilities on every admissible exact support. At T=τ log N their supports obey the exit-rate-plus-dimension rule; on irreducible competing supports, explicit prefactors and a relative discrete approximation locate crossings through the log log N and constant orders, and determine a tie-window envelope.

This is proposed framing, justified by C's current theorems rather than an external priority assertion. The distinction should identify (a) atoms, (b) the lattice-volume penalty N^(−(|F|−1)), (c) control of the maximum over the whole face, and (d) sharp cross-face comparisons. The existing complete-graph degeneracy and weak-field hierarchy show why constants matter. **Uniqueness is an enhancement, not a prerequisite for this novelty case.** [Selection](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:385>); [maxima/crossings](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:219>); [complete-graph and field consequences](<../../kagey-problems/problem131/paperC/sec_complete.tex:193>).

The phrase “first result to locate the support … for a general finite chain” should not carry the entire novelty argument even with “to our knowledge.” The direct theorem-level distinctions above are easier to defend, particularly against exact-range density theory and the unresolved Sabot–Tarrès lead. [Brydges et al., Theorem 2.1](https://arxiv.org/pdf/math/0611525); [pointwise lead](https://arxiv.org/pdf/1306.5353).

### Gaps

- No exhaustive priority clearance. No identified nearest work in this pass supplies the same complete theorem, but absence from these searches does not prove novelty.
- The Sabot–Tarrès in-preparation reference remains unresolved. Original Stadje full text and precise theorem hypotheses, original Wang–Yang, and full Kassan-Ogly–Filippov remain unverified here. The plan's instruction to remove a citation solely because only its abstract was accessible is too categorical: an explicitly limited abstract-level comparison can be honest. Remove it if it is peripheral, not because unachieved full access somehow invalidates every abstract-level citation. [Current explicit access qualification](<../../kagey-problems/problem131/paperC/sec_intro.tex:285>).

## 3. Is the proposed 50-page EJP package sensible, and which dependencies/policies need correction?

### Takeaway

**Narrowing the exposition is sensible; making submission depend on an unproved new headline theorem is not necessary.** Aim for a coherent core whose existing contribution is legible, with any unique-crossing theorem added only after proof. Paper A's public arXiv status does not impose a blanket duty to reprove its results. Official EJP instructions support full-length probability articles and template/PDF submission; they do not establish a 50-page maximum or a verified rule allowing essential proofs to be moved out. The arXiv packaging advice needs an actual compilation check, especially for `xr`. [Official EJP scope](https://imstat.org/journals-and-publications/electronic-journal-of-probability/); [official submission instructions](https://imstat.org/journals-and-publications/electronic-journal-of-probability/electronic-journal-of-probability-manuscript-submission/).

### Cited Findings

#### 3.1 Paper A: dependency audit, not mandatory duplication

Paper A is a publicly accessible preprint, arXiv:2610.06935; its current record identifies v3, 17 October 2026. A journal-under-review status does not make an available proof uncheckable. I freshly verified the arXiv record, **not every Paper A proof**. The current plan's broad assertion that C's proofs must all become independent of A is an editorial preference, not a verified EJP requirement. [Public A record](https://arxiv.org/abs/2610.06935); [EJP submission requirements](https://imstat.org/journals-and-publications/electronic-journal-of-probability/electronic-journal-of-probability-manuscript-submission/).

| Named dependency in the plan | Actual relevance found in current C | Sensible action |
|---|---|---|
| Run count | `lem:runs` already has a full multistate proof inside C. | Do not budget a redundant reproof. [Proof](<../../kagey-problems/problem131/paperC/sec_model.tex:177>). |
| Coefficientwise growth toward the middle | `prop:pair` cites A Proposition 4.1 at `sec_complete.tex:33`; concerns exact pair balancing. | Cite the public precise proposition. Alternatively use C's own complete-graph balancing result where its hypotheses/range match; it does not automatically replace every coefficientwise claim. [Pair use](<../../kagey-problems/problem131/paperC/sec_complete.tex:33>); [balancing theorem](<../../kagey-problems/problem131/paperC/sec_complete.tex:176>). |
| Uniform Bessel bound | Recalled as `eq:planar-bessel`; also supports a special symmetric-pair next-term route. | Decide whether to retain that route, cite A with exact locator, or derive the pair coefficient from C's general machinery. This is a focused dependency, not evidence that the whole local-law proof depends on A. [Bessel statement](<../../kagey-problems/problem131/paperC/sec_model.tex:99>); [next-term use](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:828>). |
| Clipped products | The general discrete-continuum proof already derives its own product bound `eq:A-kappa` and moment comparison. | Check any remaining special-pair uses individually. Avoid describing the core comparison as an unchecked import. [Internal bound](<../../kagey-problems/problem131/paperC/app_torus.tex:432>). |
| z_N expansion | Used in two-state recovery and comparison; C also derives the displayed asymptotic equation from its crossing/next-term framework. | Keep exact provenance and distinguish A's explicit all-N remainder from C's asymptotic recovery. [Two-state recovery](<../../kagey-problems/problem131/paperC/sec_complete.tex:42>). |

The prior mathematical report explicitly says the general contour/Laplace route is independent of its companion-paper Bessel cross-check, and also lists the inputs it did **not** reprove. Preserve that distinction; “the math checks found no errors” is too broad a description of a bounded audit. [Prior report, coverage and companion inputs](<../Final probability papers review/01_C_mathematical_referee.md>).

#### 3.2 Length and theorem hierarchy

The new plan says “one new headline result” but prescribes **four** headline theorems in a four-page introduction. A, B, C are already in the current introduction; D largely packages A+B plus the new uniqueness step and genericity. Giving D equal headline weight can repeat the same mechanism three times. A cleaner option is: selection rule first; sharp maxima/crossings second; complete graph as the decisive degenerate example; a concise generic-path corollary adjacent to the crossing result if proved. This is an editorial judgment, not an EJP format rule. [Current introduction A–C](<../../kagey-problems/problem131/paperC/sec_intro.tex:14>); [proposal](<C:/Users/arjun/Downloads/Paper C for EJP focused plan, new results and what to keep.md>).

Moving the long 4-cycle catalogue and reducing duplicated worked examples are low-risk ways to focus. Keep a compact example showing why a higher-dimensional support can carry almost all mass but fail to carry the mode. Keep the directed reducible example near the theorem hypotheses: it protects the scope of the Gaussian prefactor and half-log-log claim. Keep the tree constant statement, since explicit constants are part of the payoff. Higher-order calculations can be subordinated, but a retained theorem that uses the complete-face c_F value still needs a readable proof chain. [Worked example](<../../kagey-problems/problem131/paperC/sec_firstorder.tex:136>); [reducible example](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:707>); [next-term statement](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:768>).

Moving the near-vertex material out is a real thematic choice: it removes a different scale and a distinctive result imported from B. A supplement is a reasonable proposed destination; a separate short paper is **not automatically an additional publication**, and would need an independent novelty/overlap case because that material is already in public B and incorporated in C. Do not present journal suitability or publication as automatic. [Public B record](https://arxiv.org/abs/2610.09258); [C's incorporation statement and vertex theorem discussion](<../../kagey-problems/problem131/paperC/sec_intro.tex:343>).

The plan's reported 64+14 pages and prospective 50–52 pages are planning inputs, not independently rebuilt counts in this pass. Its arithmetic and page savings are rough, and adding a full score proof plus genericity can consume more space than asserted. A worthwhile 52- or 56-page theorem paper is preferable to meeting an arbitrary 50-page number by hiding essential arguments. This is an editorial inference; no official maximum was verified. [Official journal scope](https://imstat.org/journals-and-publications/electronic-journal-of-probability/).

#### 3.3 Official EJP instructions: achieved access and limits

- **Verified in current official indexed text:** EJP publishes full-length probability research and routes papers shorter than 12 pages first to ECP. This is not a 50-page ceiling. [IMS EJP page, opening description](https://imstat.org/journals-and-publications/electronic-journal-of-probability/).
- **Verified in current official indexed submission-page body:** LaTeX using the EJP template, PDF submission through EJMS, and permission to suggest referees. Direct fetching of this page returned HTTP 502 in this pass; the readable result was the search engine's indexed primary-page body. No authenticated portal inspection was done. [IMS manuscript submission, “EJMS”](https://imstat.org/journals-and-publications/electronic-journal-of-probability/electronic-journal-of-probability-manuscript-submission/).
- **Additional official preparation page found:** expressly begins “After your paper is accepted for publication,” then asks for the template, compilation checks and the necessary source/figure files. Its use of “supplementary files” for production inputs is **not** a policy certifying separate refereed mathematical supplements. These are post-acceptance directions. [IMS preparation instructions, steps 1–7](https://imstat.org/journals-and-publications/electronic-journal-of-probability/electronic-journal-of-probability-preparation-of-manuscripts/).
- The prior review verified the `ejpecp` supplement environment at class level. That is weaker than editorial permission about proof placement. No EJP-specific public supplement-refereeing/proof-placement policy was verified here. Supply any supplement with the initial submission if relying on it, and describe its proof content accurately; that is a recommendation, not a discovered rule. [Class documentation](https://ctan.math.washington.edu/tex-archive/macros/latex/contrib/ejpecp/ejpecp.pdf); [prior policy audit](<../Final probability papers review/02_C_literature_and_EJP.md>).

Do not infer that a referee will object to nonuniqueness before significance, or that a particular theorem mix buys a particular acceptance probability. The plan's percentages have no evidence base and should not guide this decision. The scope limitation is honest; whether resolving it is essential depends on the claim being sold. [Current Scope paragraph](<../../kagey-problems/problem131/paperC/sec_intro.tex:64>).

#### 3.4 arXiv: replacement versus new submission and the supplement

The official submission overview, under **“Edit or replace your submission,”** says corrected articles and errata should replace the original rather than receive a new submission. The replacement page, **“Indicate the nature of the changes,”** asks that the comments explain the revision; older versions remain public. These pages were fully accessible through the browser retrieval tool in this pass. They do **not**, in the inspected text, give a quantitative rule deciding whether a merged and substantially generalized paper C must replace B or may receive a new identifier. Thus the plan's categorical “post C as new in December” is a strategy proposal, not verified policy clearance. Preserve transparent incorporation and distinguish a genuinely new work from a revision; resolve the actual final package against arXiv's then-current guidance. [Submission overview](https://info.arxiv.org/help/submit/index.html); [replacement help](https://info.arxiv.org/help/replace.html).

The official **Submit TeX/LaTeX → “Usage of xr, subfiles, and external documents”** gives a concrete packaging warning: separately compiled PDFs are concatenated, so external-document links can fail. It describes a possible `subfiles`/internal-link setup. Current C uses `\externaldocument[S-]{supplement}`. Consequently listing two main TeX files in `00README` is not, by itself, evidence that the paper–supplement references will work. The exact ordering mechanism was not independently confirmed in the inspected current policy text. Test the actual arXiv build and resulting references before submission; no such build was attempted here. [Official TeX instructions, named subsection](https://info.arxiv.org/help/submit_tex.html); [C preamble](<../../kagey-problems/problem131/paperC/problem131_switching.tex:10>).

### Inferences

Recommended decision before implementation: approve the **expository narrowing**, retain the existing theorem-level novelty case, record the exact nonnested example, and treat the score lemma as a bounded research experiment with a clear deliverable. If it works, state the generic path on a precise logarithmic range and use the corrected null-set argument. If it does not, the current root cluster/tie-envelope theorems still support a coherent paper. Do not remove an honest limitation merely to create a “complete answer” headline. [Current crossing and window theorems](<../../kagey-problems/problem131/paperC/sec_secondorder.tex:329>).

Minimum proof deliverables before announcing D: (1) score estimate on all active branches; (2) full-interval pair uniqueness using existing root localization; (3) finite explicit genericity exceptions; (4) uniform exclusion of all nonneighbors between and within windows; (5) exact range and coexistence wording. These are mathematical dependencies, not a request to implement them during this research pass. [Relevant current sources](<../../kagey-problems/problem131/paperC/sec_secondorder.tex>).

### Gaps

- No manuscript or supplement rebuild, no arXiv test upload, no editorial communication, no policy approval, and no submission action. No acceptance forecast.
- Access record: current C sources and named prior reports were read, with focused reading of torus/Laplace and dependency passages. External PDFs/HTML were accessible as noted above, but whole-proof reading is not claimed. Existing downloaded evidence remains in [the prior local evidence directory](<../Final probability papers review/02_C_evidence/>). No external full texts were uploaded or redistributed.
- Because other local work is proceeding, these notes cite labels and source locations observed during this pass; they do not certify subsequent source changes. The earlier report's old page-placement statements are superseded by its final synthesis and the current introduction, which already leads with A and the complete-graph envelope. [Final prior synthesis](<../../reports/Final probability papers review.md>); [current introduction](<../../kagey-problems/problem131/paperC/sec_intro.tex>).
