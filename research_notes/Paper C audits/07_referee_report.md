# Referee report

**Manuscript:** *Occupation counts of rarely switching Markov chains: stratified local large deviations, modal supports and spectral reconstruction* (A. Pemmasani), submitted to the Journal of Theoretical Probability. 100 pages: 11 sections and 4 appendices.

**Version read:** `problem131_chains.tex` and the files it inputs, as of 24 October 2026. The PDF is the 07:06 build: 100 pages, no undefined references. Line numbers below refer to the `.tex` source files.

**Recommendation: major revision. I cannot recommend this manuscript for publication in its current form, mainly because of its length and scope. I would ask that it be split.**

I found no false theorem. Every statement I checked in detail is either proved or explicitly labelled as conditional. Several statements in the abstract and introduction say more than the body proves. Two pieces of the attribution need correcting. The modal-support observation model needs a better justification than the paper gives. As a single 100-page article the paper is not publishable in JTP. It contains at least two papers of different character. Part I with Part II is a solid probability paper. Part III with Part IV is an identifiability paper whose probabilistic content is thin, and which leans heavily on matrix theory (Part III) and metastability theory (Part IV).

---

## 1. Summary of the submission

A chain on $d$ states is run for $N$ steps with transition matrix $I+(T/N)Q$, and $T=\tau\log N$. The paper asks which support ("face") $F$ carries the most likely vector of occupation counts.

- **Part I** (Sections 2–6) covers the following.
  - Run expansion and continuum density (after Good 1961).
  - The killed Donsker–Varadhan (DV) functional $J_F$ and the restriction identity $J_F=J_V|_{\Delta_F}$.
  - First-order face selection by $\Phi_\tau(F)=\tau\lambda_F+|F|-1$, with winners read off a convex hull.
  - A local limit theorem in each face: $f_T=T^{(k-1)/2}C_F(\alpha)e^{-TJ_F}(1+O(1/T))$, uniform in $T\ge1$.
  - Face maxima with explicit constants $K_F$, the crossing equation with the universal $\tfrac12\log\log N$, and tie windows.
  - Tree formulas for $K_F$, and a weak field.
  - A boundary layer at a facet, with a Bessel kernel.
- **Part II** (Sections 7–8): the complete graph, with exact balancing, exactly one mode change, the effect of a start and of a weak field, and the near-vertex layer.
- **Part III** (Section 9): which functionals of the law determine $Q$.
  - Under calibrated fields and time scales, the boundaries of the strict modal-support regions determine a reversible $Q$ from $m+d-1$ coordinates. This comes with minimality, Lipschitz stability and a finite-horizon version.
  - In general the boundaries determine all principal minors of $-Q$, and the generators sharing them are described through the cut-transpose theory of Loewy, Al Ahmadieh and Chatterjee–Ghosh–Gurjar–Raj.
  - The DV functional carries exactly the same information (Corollary 9.2).
- **Part IV** (Section 10): low temperature with $q_{ij}=e^{-V_{ij}/\eta}$. The depth of a face is the largest cycle depth it contains. Away from critical heights the winners are cycles of least size. At a critical height a finite prefactor problem decides, and an example has a noncycle winner. Calibrated rewards read off cycle depths, cycles are characterized by depths, and window endpoints give prefactors.

---

## 2. Correctness

I read every proof in the main text. I checked the parts written this week line by line, and the older appendices (local law, Laplace lemma, complete graph, near vertex) at the level of the main steps. I also recomputed three things in exact arithmetic:

- the $4\times4$ cut-transpose example after the proof of Theorem 9.12, including $Q'$, all 15 principal minors, $Q'_Y=Q^*_Y$ and $q^*_{12}=351/530$;
- the determinants and limiting Green matrices $B_F$ of Example 10.5;
- the hand checks in Example 7.8, Example 7.10 and Corollary 7.12.

All of these agree with the text.

### 2.1 The killed functional (`sec_dv.tex`)

- **Proposition 3.1 (restriction identity).** Correct. The proof is two lines, letting $u\downarrow0$ off $F$. As the text itself says, the identity is elementary. It should be presented as a remark or a lemma, not as a proposition carrying conceptual weight.
- **Lemma 3.2 (monotonicity).** Correct. It uses strict monotonicity of the Perron root under $0\le\widetilde B\lneq B$ with $B$ irreducible. The last sentence refers forward to $\Phi_{\tau,v}$ in Section 9.1, which is not yet defined (lines 79–81).
- **Proposition 3.3.** Correct.
  - The resolvent test vector $u=(sI-B')^{-1}\ones$ for the lower bound on every face is neat.
  - The criterion (the maximizer exists exactly when $\alpha$ is stationary for $G^\psi$) is right.
  - Strict convexity and the boundary case of (a) via (d) are right.
  - (c) is the classical reversible formula.
- **Proposition 3.4.** Correct and classical (Donsker–Varadhan, Collatz–Wielandt). The Legendre inversion through $v=q-A_Fr_\alpha/r_\alpha$ is right.

### 2.2 First order (`sec_firstorder.tex`)

- **Theorem 4.2.** Correct.
  - In (ii) the lower bound with $T^{k_F-k^*}$ is weaker than the expected power $T^{(k^*-1)/2+k_F-k^*}$. The author says so in Section 11. It is consistent with the explicit reducible example: for $F=\{1,2\}$ in Example 5.15, $k^*=1$ and the power is $T^1$.
  - The appendix proof (Claims A and B) is fine.
- **Theorem 4.4 (hull).** Correct.

### 2.3 Second order: field-first local law, face maxima, weak field (`sec_secondorder.tex`)

- **Definition 5.1 and Proposition 5.2.** Correct.
  - I rechecked the reversible determinant $\det\Sigma_\alpha=2^{k-1}(\prod\alpha_i)^2/\tree(c(\alpha))$ through the identity $\Sigma=2(D'-\alpha'\alpha'^\top)\mathcal L_{(1)}^{-1}(D'-\alpha'\alpha'^\top)$. I also rechecked Corollary 5.3, where $K_F=\mu(F)k^{(k+1)/2}\sqrt{\tree}\,(4\pi)^{-(k-1)/2}$.
  - The specializations are right: $1/\sqrt{2\pi}$ for a pair of the 4-cycle, and $k^{k+1/2}/d$ on the complete graph.
- **Field-first local law (Theorem 5.4).** Correct. Since $e^{Tv\cdot\alpha}$ multiplies both sides exactly, the field is cosmetic in this statement. The text says so (lines 195–196). Writing it with $v$ adds nothing, and I would state it with $v=0$.
- **Theorem 5.6 (stratified local law).** A correct combination of Theorem 5.4, Lemma 5.5 and Proposition 3.1.
- **Theorem 5.7 (face maxima, uniform over compact sets of fields).** Correct.
  - The split into a ball $U(v)$ and its complement is uniform in $v$: lower semicontinuity of $J^v$ on the compact set $\mathcal E$ gives the margin $3\eta$, and finitely many tilts $\theta_j$ cover it.
  - The maximizer bound $|\hat x|=O(1/T)$ uses $T^2/N\le1/T$. This is where the exponent $\tfrac13$ enters, as stated.
- **Theorem 5.8 (crossing equation) and Theorem 5.9 (tie windows).** Correct.
  - I checked $\ell_F$, the identity $t_j=b_{FG}$ at a kink, and the two cases $\Delta=0$ and $\Delta>0$ in (iii).
  - The "consequence" paragraph is right: $E-\ell_G$ is convex and piecewise linear, so its zero set is an interval with kink endpoints.
- **Proposition 5.11 and Example 5.15.** Correct. I checked Example 5.15 ($K=(1+2b)^2/(2\sqrt3\pi b)$).
- **Proposition 5.17 (weak field).** Correct.
  - (b) uses $\nabla\lambda_F(0)=-\alpha^*_F$ and the uniformity of Theorem 5.7 on $\{s\xi\}$.
  - (c) correctly re-runs Theorem 5.9 with $\kappa+\|\xi\|$.

### 2.4 Boundary layer (`sec_boundary.tex`)

- **Exact representation (Lemmas 6.1 and 6.2).** Correct.
  - I checked the marked-word bookkeeping, including the identity $\binom{n+\varrho-1}{\varrho-1}/(n+\varrho-1)!=1/(n!(\varrho-1)!)$ that produces the diagonal shift $d(z)$.
  - The entire-function claim and the contour form are right.
  - This is the most original idea in Part I after the local law.
- **Pair faces (Proposition 6.3).** Correct.
  - With $z=z_*t$, the three moments give $\sqrt{\omega s/x}I_1$, $(q_{ji}+\frac{\mu_i}{\mu_j}q_{ij})I_0$ and $\frac{\mu_i}{\mu_j}\sqrt{\omega x/s}I_1$.
  - The two-sided bound follows from Amos's inequality $I_1/I_0\ge\zeta/(1+\sqrt{1+\zeta^2})$.
  - The claim that $\sqrt{x/T}$ is attained is right.
- **Constants (Proposition 6.4).**
  - (i) The exchange of suprema with $2\sqrt{xSP}=\inf_z(SzP+x/z)$ is right.
  - (ii) The Hessian of the jump term at $\psi_0$ is the Laplacian $\mathcal L_\beta$ with conductances $\kappa$. Differentiating the critical equation gives $\psi'(0)=-\mathcal L_\beta^+\nabla P$ and $\partial_z^2J=\nabla P^\top\mathcal L_\beta^+\nabla P=2\omega_\beta(\gamma_\beta-q_i)$. Correct.
  - (iii) Correct as a two-term expansion. The bootstrap from $O(\varepsilon^{1/2})$ to $O(\varepsilon)$ for $\psi^*-\psi_0$ is implicit, and one sentence would make it explicit.
  - (iv) Reversibility of $Q_G(z)$ with respect to $\nu_G$ makes $J_G(\beta,z)$ exactly linear in $z$, which gives the closed form $J_F=SJ_G+q_ix-2\sqrt{\omega Sx}$. Correct.
- **Prefactor matching (Proposition 6.5).** Correct. The powers $\epsilon^{1/4}$ from the tree and $\epsilon^{-1}$ from $\prod\alpha$ combine to the stated power.
- **Two-state-facet lemma (Lemma 6.6).** Correct.
  - The word sums are $\sqrt{\tau s_1/s_2}\,I_1(\xi)$ and $I_0(\xi)$.
  - The sector $|\arg\xi|\le\pi/12$ and the DLMF 10.40.1 expansion are right, and $U+V>0$ at $z=0$ by $\mu(G)>0$.
  - **The theorem is therefore unconditional for $|F|\le3$, as the body says.**
- **Theorem 6.7 (facet layer).** Correct under its hypotheses.
  - (a) In the few-visit regime the choice $\rho=\max(z_*,1/S)$ is checked. In the many-visit regime the steepest-descent bound $\operatorname{Re}\lambda(z)-\lambda(\rho)\le-\frac\zeta2(1-\cos\phi)$ follows from $S\rho^2\le Cx$ and $x/\zeta\le C\sqrt\delta$.
  - (a) cont. The lower bound uses "the uniform form of Lemma B.1, which has the same proof". That is true, but the uniform version should be stated as a lemma in Appendix B, since it is used with non-compact parameters.
  - (b)–(c) The reversible two-term form and the general logarithmic form are right. I checked the $x\le1$ expansion with $I_{2m-1}/I_1$, and the $1\le x\le\delta T$ saddle shift $O(\zeta x/S+1/\zeta)$.
  - The error in (b), $\sqrt{x/T}(1+x)$, is of order $T$ when $x\asymp T$. So (b) has content only for $x\ll T^{1/3}$. Beyond that, (a) is the statement. The text says this, and the theorem would read better with (b) restricted to that range.
- **Conditional general statement.** The text marks it correctly as conditional on Lemma L, and the "route" paragraph (lines 434–456) as not completed. Two pieces of the section are not proved and are not theorems: that route paragraph, and the conjectural lattice display in Remark 6.8 (lines 618–643). They are honest, but they should be shortened to one paragraph of open problems, or deleted.

### 2.5 Complete graph and near vertex

Correct, as far as I checked:

- the monotonicity of $p_{N,k}$ via the injection $W_n(j)\le W_{n+e_i}(j)$;
- the strict increase of $W_n(k)=k!(k-1)(N-k)/2$;
- the log-concavity of $B_n(w)$;
- the order $a_2>a_3>\cdots$;
- Example 7.10 ($t_{\rm ef}=\tfrac12\log(32\pi/243)$, width $\log\frac{16}{9\sqrt3}$);
- Corollary 7.12 ($H>3/4$ is exactly what $c''\le\tfrac12$ needs).

### 2.6 Reconstruction (`sec_reconstruction.tex`)

- **Proposition 9.1 (controlled score law).** Correct. It is Remark 4.3 restated, and the two should be merged.
- **Lemma 9.3 (suppression).** Correct.
  - Wholly suppressed faces have a gap of at least $\tau(\bar v-R)\ge\tfrac34+UR$.
  - Mixed faces satisfy $e-1/(4U)\le\lambda_F\le e$ via the $2\times2$ Schur bound.
- **Theorem 9.4 (reversible reconstruction).** Correct.
  - In (a) the pair loses by $\ge1-\tau_0R=\tfrac12$.
  - In (b), $\lambda_{\{i,j\}}=a-g$ and $t_{ij}=1/g$, with $1/R\le t_{ij}\le(\sqrt{13}+3)R/(2b^2)<U/2$, and the inversion formula holds.
  - (c) is the ground-state reconstruction.
- **Theorem 9.5 (minimality).** Correct. It is a standard constant-rank argument.
- **Theorem 9.7 (stability).** Correct.
  - I checked $|\widehat w-w|\le(\tfrac{20}3+\tfrac{28}9)\varepsilon$.
  - The constants $\phi_*$ and $g_*$ follow from $q_l\phi_l\ge\eta\phi_k$ and a spanning-tree Poincaré inequality.
  - The Davis–Kahan step is right.
- **Lemma 9.8 (irreducibility of $R_F$).** Correct.
  - The cycle-minimality argument shows $\det(-Q_U)<\det(-Q_{U\cap X})\det(-Q_{U\cap Y})$, which contradicts the split.
  - It is a special case of Al Ahmadieh, Lemma 5.1, which the text acknowledges.
- **Lemma 9.9 (Perron branch).** Correct.
  - The map $y\mapsto\psi(v^0+(0,y))'$ has Jacobian determinant $\beta_1>0$, so the projection contains an open set.
  - Then $\mathcal D\equiv0$, $\widetilde R\mid p_1R'_F$, and $\widetilde R\nmid p_1$.
- **Lemma 9.10 (suppression without reversibility).** Correct, with the Collatz–Wielandt test vector. The condition on $\bar v$ is sufficient as written.
- **Lemma 9.11 (exposure by descent).** Correct.
  - Genericity: $v=te_j$ separates $\rho_{H_1}$ from $\rho_{H_2}$, using $\lambda_F\ge-t$ and $\lambda_{H_1}\le q_j-t$.
  - (i): below the hypersurface $\Phi(H)-\Phi(G)=[\Phi(H)-\Phi(F)]+[\Phi(F)-\Phi(G)]>0$ because both brackets are positive, and above it $\Phi(H)-\Phi(F)\ge\kappa$.
  - Outside faces lose by $\tfrac12$ to a component $C$ of $G'\cap F$.
  - Induction: pairs fix $c=q'_1-q_1$, continuity forces $\Phi'(F)=\Phi'(G)$ on the hypersurface, Lemma 9.9 extends the identity, and $\lambda_V(0)=0$ gives $c=0$.
  - One gap of exposition: in the pair step the ranges of $\tau$ and $\bar v$ depend on $Q'$ (line 638: "$\tau$ in a compact subinterval of $(0,1/(2\max(q_{\max},q'_{\max}))]$"). That is legitimate for an identifiability statement. But the text should say explicitly that, unlike in the reversible case, no design is fixed in advance here.
- **Theorem 9.12 (non-reversible reconstruction).** Correct.
  - (N) is the key normalization and is right. It uses a positive null vector of an irreducible Z-matrix with the spectrum of $-Q$, and uniqueness over all real invertible diagonal similarities.
  - (b) is right, and the determinant argument is fine.
  - (c) and (e) are Loewy and Hartfiel–Loewy plus (N). One point is left implicit: a complex diagonal similarity between real irreducible matrices can be taken real, because edge ratios are real and the graph is connected.
  - (d), cut-transpose: I checked the Schur-complement proof that minors are preserved. The rule that $\operatorname{diag}(D_X,D_Y)$-similarity changes the cut-transpose by $\operatorname{diag}(D_X,D_Y^{-1})$ is right. So is the reduction of the CGGR sequence (Theorem 1.1 there, $k<2n$, Remark 2.11) to the paper's nonnegative factorizations up to diagonal similarity. A symmetric matrix is its own cut-transpose.
  - (f): I checked $W\ne0$ via $r(te_j)/\max r\to e_j$, the time-reversal formulas $r^*=D_\pi^{-1}l$ and $l^*=D_\pi r$, the path-reversal identity, and the null vector $x=(\ones_X,s_0\pi_Y)$ of $C'$, which gives $Q'_X=Q_X$ and $Q'_Y=Q^*_Y$.
  - Parts (a)–(f) are proved.
- **Corollary 9.2 (three-way form).** Correct in all four directions.
  - (iii)⇒(i) handles the boundary of the simplex by convexity and lower semicontinuity.
  - (iii)⇒(ii) uses Lemma 9.8 to show that $Q$ and $Q'$ have the same irreducible faces.
- **Proposition 9.14 and Theorem 9.15 (finite horizon).** Correct.
  - I checked $x_{i,N}$ and its expansion, the window argument with $\Xi'\ge2/U$, and $c_{ij}=-t_{ij}(\tfrac12\log t_{ij}+\log(K_{ij}/\mu_i))$.
  - I also checked Remark 9.17 numerically: $t_{12}=6.16$ and $K_{12}/\mu_1\approx5.9$, consistent with $c_{12}=-16.5$.
  - The uniformity proof of Proposition 9.14 is a list of the form "every constant is continuous on a compact set". It is convincing but long, and could be cut to a paragraph.
  - Remark 9.16 is correct: the ratio is exactly 2, and the switch sits at $1+4\log2/L$.

### 2.7 Low temperature (`sec_lowtemp.tex`)

- **Theorem 10.1 (depth).**
  - The exit-time sandwich $1/M^{\rm exit}_F\le\lambda_F\le|F|/M^{\rm exit}_F$ is correct and self-contained.
  - The depth identity rests on one external statement: the exponential order of the mean exit time from an *arbitrary* domain is the largest depth among the maximal cycles contained in it. The author cites "Catoni, Proposition 4.2, Definition 4.3 and Proposition 4.11". I could not verify from the citation alone that this is exactly the statement there, for a general domain and for the maximum of $\E_i\tau$ over starting points.
  - The author should quote the result verbatim, with its hypotheses, in particular how the diagonal entries of $P_\eta$ enter Catoni's rare-transition assumption.
  - The rest of the proof is fine.
- **Theorem 10.2 (noncritical rule).** Correct. A deep face of least size is a cycle, by Theorem 10.1.
- **Proposition 10.3 (prefactors).** Correct: cofactor asymptotics, $D(F)=\max_je_{jj}$, $B_F$ and continuity of the spectral radius. **But this is classical in substance.** The logarithmic asymptotics of the principal eigenvalue of a killed generator with entries $e^{-V_{ij}/\eta}$, and the graph and determinant expressions behind it, are in Wentzell (1972), and in Freidlin–Wentzell, Chapter 6, on eigenvalues. Neither is cited at this point. See Section 3 below.
- **Theorem 10.4 (critical windows).** Correct.
- **Example 10.5.** Correct. I recomputed $\det(-Q_{12})=2t^4+\dots$ and $\det(-Q_{123})=\det(-Q_{124})=2t^6+\dots$, and the limiting Green matrices $B_{12}$, $B_{123}$, $B_{124}$ with spectral radii $\tfrac12,\tfrac32,\tfrac12$. This gives $a_{12}=2$, $a_{123}=\tfrac23$, $a_{124}=2$, the windows $(0,\tfrac34)$, $(\tfrac34,\tfrac32)$, $(\tfrac32,\infty)$, and the width $\log2$. The cycle structure follows from the energy criterion.
- **Example 10.6 (branch switch).** Correct.
- **Lemma 10.10 (laminarity) and Lemma 10.12 (nested strictness).** Correct, by a rounds and Wald argument for nesting. Both are standard facts of cycle theory (Catoni; Olivieri–Vares, Chapter 6) and should be cited rather than reproved, or at least credited.
- **Lemma 10.11 (killed depth).** Correct. The cemetery chain makes Theorem 10.1 applicable. The constant called $L$ at line 618 clashes with $L=\log N$ and should be renamed.
- **Theorem 10.13 (attraction).** Correct. I checked all five cases in (b). The case where $G$ meets $C$ without containing it uses laminarity and Lemma 10.11, with $D^K(G)\le\max(D^-(C),\gamma)<h$.
- **Theorem 10.14 (cycles from depths).** Correct, given Lemma 10.12 and Theorem 10.1. It may be known: see Section 3.
- **Theorem 10.15 (prefactors from window endpoints).** Correct. The bracket $\tfrac23\le a_{124}\le2$ in the example is right.
- **Lemma 10.8 and Proposition 10.9.** These form the suppression block. They are correct, and they are negative results ("suppression does not read the depth"). They cost about 2.5 pages and could be one remark.

### 2.8 Summary on correctness

There are no errors in the proved statements. There are four places where the text leans on something unstated:

1. **Appendix B:** the uniform Laplace lemma, used in Theorem 6.7(a).
2. **Lemma L, real $z$:** the claim that "the proof of Theorem 5.4 needs only one change" for the end vector $e^{(z)}$, which identifies $C_G(\beta,z)$.
3. **Theorem 10.1:** the exact statement taken from Catoni.
4. **Theorem 9.12(c), (e):** real versus complex diagonal similarity.

All four are easy to repair.

---

## 3. Abstract, introduction and credit to prior work

**Claims that say more than the body proves, or are inconsistent with it:**

1. **Abstract (`problem131_chains.tex` lines 69–71).** It says the Bessel layer is "proved for pair faces with an explicit error and for larger faces under one stated lemma". The body (`sec_boundary.tex` lines 9–11 and 226–227) proves it unconditionally for faces of at most three states. This sentence understates rather than overstates, but it is inconsistent and must be fixed.
2. **Abstract (lines 81–82).** "Noncycles win on open windows" should say *open windows of the rescaled coordinate $x$ at a critical height*. At every fixed noncritical height the winner is a cycle (Theorem 10.2), and the window collapses to a single height. Without this qualifier a reader will think Theorem 10.2 is contradicted.
3. **Introduction (`sec_intro.tex` lines 226–228).** "The largest field exponent at which the face still wins is its depth" holds for **cycles** only (Theorem 10.13(b)). For a general face the threshold is at most the depth, and $D(F)=\max_{G\subseteq F}\tau(G)$.
4. **Introduction (lines 84–86) and Section 7.4.** "Shifts the lines … by the field averaged over each face" should say *averaged against the quasi-ergodic law $\alpha^*_F$*. The uniform average is specific to the complete graph.
5. **Introduction (lines 205–206) and `sec_reconstruction.tex` line 138.** "The time-reversal ambiguity belongs to the occupation data and not to the observation" is misleading. Theorem 9.12(f) shows that for a generic start the full law of the counts *does* separate $Q$ from $Q^*$, because $K'_V\neq K_V$ forces different face maxima. The ambiguity belongs to the logarithmic scale $J_V$ and to the stationary start, not to occupation data as such. Please rephrase, for example: "the ambiguity is a feature of the logarithmic scale and of the stationary start, which no count statistic can resolve".
6. **Introduction (lines 189–195).** The non-reversible statement reads as if a design were fixed in advance, as in the reversible case. It is an identifiability statement: the fields used depend on the generators being compared (see Section 2.6 above). Say so.

**Credit.**

- **Good 1961.** The run expansion and the continuum density are credited to Good's (3) and (10), and the saddle-point suggestion to pp. 42–43. This is appropriate, provided the page reference is exact; I could not check it.
- **Kim and Landim, Section 5.** The paper's description is accurate for their Lemma 5.1, Corollary 5.3 and Example 5.4. Three adjustments:
  - (a) Lemma 5.1 recovers exit rates and products, the minors of orders 1 and 2, and Corollary 5.3 *also uses $I^{-1}(0)$*, that is, the stationary laws (Lemma 5.2). It is fair to say "orders one and two plus the stationary law".
  - (b) Their stated aim (Section 5, opening) is "optimal conditions on $(V,E)$ such that $I=\tilde I$ implies $X\equiv\tilde X$". "Their question, which generators share $J_V$" (`sec_reconstruction.tex` line 727) is a natural extension of that aim, not their question. Say "the question left open by their Example 5.4".
  - (c) Their Corollary 5.8, that the joint measure–current (BFG) functional determines the generator when all states are recurrent, should be mentioned. It is the direct contrast to Corollary 9.2: adding the current removes the whole fiber.
- **Loewy, Hartfiel–Loewy, Engel–Schneider, Al Ahmadieh, CGGR.** Accurately described, and the "borrowed versus new" paragraph (`sec_reconstruction.tex` lines 712–738) is essentially fair. One omission: part (b), that every matrix in the fiber of an irreducible matrix is irreducible, is Al Ahmadieh's Corollary 5.6. It should be cited at line 771, where the text says "the same argument applies to every real matrix".
- **"What this paper adds".** With the above, the three items are accurate: the generator translation (N), reading the minors off the modal-support map, and the amplitude obstruction. But the first item is short (a Perron–Frobenius normalization) and should not be given equal billing with the other two.
- **Perron-branch lemma.** The comparison with Delmas–Dronnier–Zitt is appropriate. I would also ask for a literature check of two lines of work:
  - the convexity of the Perron root in the diagonal and its link to the DV variational formula (J. E. Cohen 1979–81; S. Friedland, "Convex spectral functions", 1981);
  - inverse problems recovering a matrix from the spectral radius of $A+D$.
  
  I do not claim the lemma is in that literature, but a JTP reader will ask.
- **Pedler and Kovchegov–Meredith–Nir.** Fair: "facet version of Pedler's formula" is the right description of Proposition 6.3.
- **Catoni and Cirillo–Nardi–Sohier.** Fair for the depth identity. Missing:
  - Wentzell (1972) and Freidlin–Wentzell, Chapter 6 (eigenvalue asymptotics and $W$-graph formulas). These make Proposition 10.3 classical in substance.
  - Trouvé (1996, cycle decompositions), and Olivieri–Vares, Chapter 6, for laminarity, strict growth along nested cycles, and possibly the characterization in Theorem 10.14.
  - The potential-theoretic prefactor literature (Bovier–den Hollander; Landim's survey and the non-reversible Eyring–Kramers work).
  
  The claim "what is new is … the prefactor rule at critical depths" (`sec_intro.tex` lines 295–297; `sec_lowtemp.tex` lines 23–26) should be narrowed. The prefactors themselves are classical. The new part is their role in deciding the dimension-versus-rate competition.

---

## 4. The observation model

The data in Part III are the boundaries between the regions of $(\tau,v)$ where one face is the unique minimizer of $\Phi_{\tau,v}$. They are read in the limit $N\to\infty$ at each point, under calibrated killing ($v\le0$) and a calibrated time unit.

**What the text justifies well.**

- Section 9.1 explains that a nonpositive field is a known killing rate.
- It explains that $P_N(n)e^{Tv\cdot n/N}$ is the probability of surviving with composition $n$, and that the mode does not see the normalization.
- It explains that a constant shift of $v$ changes no winner.
- Ties are excluded cleanly, through a closed nowhere-dense set.
- The reversible design is genuinely an experiment fixed in advance by $R$, $b$ and the labels. The finite-horizon theorem quantifies the bias $\log\log N/(2\log N)$ and shows that the start bound is needed.

**What it does not justify.**

1. *Why the argmax-support is the observable.* It is a deterministic functional of the whole law, not something estimated from a few trajectories. An observer with access to the modal support of the killed law could equally read the survival probability $\sum_nP_N(n)e^{Tv\cdot n/N}\approx e^{-T\lambda_V(v)}$. That quantity gives $\lambda_V(v)$ for all $v$, hence all principal minors, by Lemma 9.9 alone, with no exposure descent and no suppression lemmas.
   
   The paper motivates the modal support as "the coarsest functional", and as a mathematical question that is legitimate. But the text should
   - state this comparison openly;
   - explain what the descent through faces buys, namely that it needs only a finite label at each point;
   - say why such a label might be available while the survival probability is not.
2. *Calibration.* Both $\tau$ and $v$ are assumed known in the units of $Q$. This is assumed and discussed (Remark 10.16 for Part IV), but the introduction should state it as a standing hypothesis of Part III.
3. *Starts.* Full support is used everywhere in Part III, and $\min\mu_i\ge\mu_*$ in the finite-horizon theorem. That is fine and stated.

Overall the model is coherent and honestly stated. It is somewhat artificial as statistics, and acceptable as an identifiability framework, provided the comparison in point 1 is made.

---

## 5. Novelty and significance (as a JTP referee would judge them)

**Main contribution.** Part I: a precise, uniform description of the law of the occupation counts of a slowly switching chain on every face at the scale $T\asymp\log N$. It has these components:

- the stratified local law with explicit constant $C_F(\alpha)$ and relative error $O(1/T+T^2/N)$, uniform in $T\le N^{1/3}$;
- the face-selection rule via the hull of $(\lambda_F,|F|-1)$;
- the universal crossing equation $\delta T+\frac\Delta2\log T=\Delta\log N-\log(K_F/K_G)+O(1/\log N)$ with its $\tfrac12\log\log N$;
- tie windows;
- the tree and forest formulas for $K_F$.

This is a real contribution and within JTP's scope. The local law is a careful saddle-point analysis (Good's suggestion carried out) with uniform constants, and the explicit forms of the constants (Propositions 5.2(b) and 5.11) are pleasant. The complete graph (Part II) is a satisfying worked case with exact statements at every $N$.

**Second contribution.** Corollary 9.2 and Theorem 9.12: the DV functional and the controlled boundaries carry exactly the information of the principal minors. The fiber is $\{Q,Q^*\}$ without a cut, and finite in general, with a blockwise $Q/Q^*$ description of cut-transposes. It answers cleanly the question left open by Kim–Landim's Example 5.4. Its probabilistic content is short:

- $J_V\leftrightarrow\lambda_V(\cdot)$ by Legendre duality;
- $\lambda_V(\cdot)$ on an open set determines $\det(-Q-\operatorname{diag}w)$, by irreducibility of that polynomial;
- the rest is matrix theory due to others, plus a normalization.

I regard it as a nice note rather than a major result.

**What is routine** (proved correctly, but standard):

- the restriction identity;
- the variational formula;
- monotonicity of exit rates;
- minimality, a rank argument;
- stability, standard perturbation theory;
- the uniformity bookkeeping of Proposition 9.14;
- laminarity and nested strictness of cycles;
- the prefactor proposition, classical in substance;
- the depth theorem, a short consequence of Catoni.

**Moderately new but partial.**

- The boundary layer. The contour representation is new and the three-state case is proved, but the general case is conditional.
- The low-temperature selection rule. Noncritical winners are cycles of least size, and the four-state example shows that a noncycle can win at a critical height. It is pleasant, but it follows quickly from Theorem 10.1 once Part I is in place.
- The attraction design and Theorem 10.14 are neat, but the novelty of the characterization of cycles by depths needs checking against Catoni and Trouvé.

---

## 6. Length

At 100 pages the paper is roughly three times what JTP can reasonably carry for this content, and its four parts address different audiences. **I would ask for a split.** My suggestion:

- **Paper 1 (JTP):** Sections 2–5 plus 6 restricted to $|F|\le3$, and 7, with Appendices A–C. Section 3 becomes about 2 pages; Section 8 and Appendix D go.
- **Paper 2:** Section 9.3 with Corollary 9.2 and the minimal parts of 9.1–9.2, as a short note of about 12–15 pages. The DV-functional fiber with the cut-transpose translation. It would suit ECP or a probability/linear-algebra venue.
- **Paper 3, optional:** the reversible design with stability and finite horizon, together with Part IV, about 20–25 pages.

If the author prefers one paper, it must come down to roughly 50–60 pages. Specific cuts with page estimates (current PDF page ranges):

| Item | Current pages | Suggested | Saving |
|---|---|---|---|
| §4.1 worked 4-cycle example, table and figure (pp. 14–17) | ~3 | half a page of text, keep the figure | 2–2.5 |
| §3: restriction identity, monotonicity, Props 3.3–3.4 (pp. 10–14) | ~4 | 2: cite DV and Berman–Plemmons for the classical parts | 2 |
| §5.4 forest formula, Prop 5.11 and Lemma A.3 (pp. 27–29, 88–90) | ~4 | state Prop 5.11(b) only, proofs to supplement | 3 |
| Remark 5.14 (flows) and Remark 5.16 (next term) | ~1 | delete or 3 lines | 0.8 |
| §6 route to Lemma L (lines 434–456), Remark 6.8 (lattice layer), §6.7 heuristic, §6.8 near-vertex comparison, §6.9 numerics | ~4 | one paragraph of open problems | 3.5 |
| §6 conditional $k\ge4$ statement | — | drop from theorem, keep as a conjecture | 0.5 |
| §7: Remark 7.4 (other graphs), Example 7.8 (finite $N$), start-balancing counterexample, one of Corollaries 7.11 and 7.12 | ~2.5 | 1 | 1.5 |
| §8 near vertex and App. D (pp. 49–50, 94–96) | ~4.5 | delete: it is from the companion preprint and the text calls it a "worked case" | 4.5 |
| Prop 9.1 duplicating Remark 4.3; duplicate definitions of $\lambda_F(v)$, $M_F(T,v)$, $K_F(v)$ (`sec_dv` 61–66, `sec_secondorder` 252–257, `sec_reconstruction` 38–41, 964–969) | ~1.5 | define once | 1 |
| Thm 9.5 (minimality) and Remark 9.6 (partial data) | ~1.5 | a remark | 1 |
| Prop 9.14 uniformity proof | ~2 | half a page | 1.5 |
| Remarks 9.16–9.17 | ~1 | keep 9.16 only | 0.4 |
| §10.2: unperturbed path (Prop 10.7), suppression block (Lemma 10.8, Prop 10.9 and the two-state and three-state discussion) | ~3.5 | one remark | 2.5 |
| Lemmas 10.10 and 10.12 | ~1 | cite Catoni and Olivieri–Vares | 0.7 |
| Example 10.6 (branch switch) | 0.5 | delete | 0.5 |
| §11 verification | ~3 | 1, details to the repository README | 2 |

The total is about 28–30 pages, which gives roughly 70 pages. That is still too long for one JTP article, hence my request for a split.

---

## 7. Specific corrections (file and line)

1. `problem131_chains.tex` 69–71: the layer is unconditional for $|F|\le3$; correct the abstract.
2. `problem131_chains.tex` 81–82: "noncycles win on open windows" should specify windows of the rescaled coordinate at critical heights.
3. `problem131_chains.tex` 130–141: the "earlier version" and `removed_proofs` are repository files. For a journal submission, cite arXiv versions or a supplementary file, not repository paths.
4. `sec_intro.tex` 84–86: "averaged over each face" should read averaged against $\alpha^*_F$.
5. `sec_intro.tex` 205–206 and `sec_reconstruction.tex` 136–138: rephrase the time-reversal sentence (Section 3, item 5 above).
6. `sec_intro.tex` 226–228: attraction reads the depth of a *cycle*; for general faces only $\tau(G)\le D(G)$.
7. `sec_intro.tex` 295–297 and `sec_lowtemp.tex` 23–26: narrow "the prefactor rule" and cite Wentzell 1972 and Freidlin–Wentzell, Chapter 6.
8. `sec_intro.tex` 189–195: state that the non-reversible result is identifiability, with no fixed design.
9. `sec_dv.tex` 79–81: forward reference to $\Phi_{\tau,v}$; define it here, or drop the last clause.
10. `sec_dv.tex` 29–56: downgrade Proposition 3.1 to a lemma. The surrounding prose overstates its role.
11. `sec_secondorder.tex` 186–196: state Theorem 5.4 with $v=0$; the field is an exact factor.
12. `sec_secondorder.tex` 252–257, `sec_firstorder.tex` 269–285 and `sec_reconstruction.tex` 38–44, 64–101, 964–969: merge the duplicate definitions and merge Proposition 9.1 with Remark 4.3.
13. `sec_boundary.tex` 284–293 (Prop 6.4(iii)): add the bootstrap from $O(\varepsilon^{1/2})$ to $O(\varepsilon)$ for $\psi^*-\psi_0$.
14. `sec_boundary.tex` 381–384 (after Lemma L): the identification of $C_G(\beta,z)$ for real $z$ through a modified Theorem 5.4 should be a stated lemma, or at least a precise remark.
15. `sec_boundary.tex` 487–489: "holds only for $x\le CT^{1/3}$". The numerics support that the bound is sharp, but it is not proved. Say "our bound gives the relative form only for …".
16. `sec_boundary.tex` 553–561: state the uniform Laplace lemma in Appendix B instead of "which has the same proof".
17. `sec_boundary.tex` 434–456 and 618–643: shorten the unfinished route and the conjectural lattice display to an open-problems paragraph.
18. `sec_boundary.tex` 445–446 and the end of §6.6: restrict Theorem 6.7(b) to $x\le CT^{1/3}$, or say that its error is of order $T$ near $x\asymp T$.
19. `sec_complete.tex` 194–196: "the earlier arXiv version of this work [paperB]" conflicts with the bibliography title and the Acknowledgments ("the preprint … which this paper incorporates"). Use one description throughout. The same applies to "version 1 of [paperB]" in `sec_vertex.tex` 82.
20. `sec_reconstruction.tex` 3–10, `sec_lowtemp.tex` 3–8 and 372–374, `sec_dv.tex` 3–5: remove the internal source comments (paths to working notes) before submission. arXiv publishes the source.
21. `sec_reconstruction.tex` 106–118: turn "same controlled boundaries" into a numbered definition that lists exactly the field families used: the pair designs, $(v_F,-\bar v)$ with $\bar v$ large, and the starts.
22. `sec_reconstruction.tex` 638: make explicit that the ranges depend on both generators.
23. `sec_reconstruction.tex` 727: "Their question …" should read "the question left open by their Example 5.4". Add a sentence on their Corollary 5.8 (the BFG functional determines $Q$).
24. `sec_reconstruction.tex` 771: cite Al Ahmadieh, Corollary 5.6, for irreducibility of the fiber.
25. `sec_reconstruction.tex` 778–783 (proof of (c)) and 833–839 ((e)): note that the diagonal similarity can be taken real for real irreducible matrices.
26. `sec_lowtemp.tex` 117–137: quote verbatim the Catoni statement used (exit time from a general domain), with its hypotheses.
27. `sec_lowtemp.tex` 182–220: credit Wentzell (1972) and Freidlin–Wentzell, Chapter 6, for the eigenvalue asymptotics and the determinant formula.
28. `sec_lowtemp.tex` 593–604 and 649–676: cite Catoni and Olivieri–Vares for laminarity and the strict growth of depths along nested cycles. Check Trouvé (1996) for Theorem 10.14.
29. `sec_lowtemp.tex` 618: rename the constant $L$ (it clashes with $L=\log N$).
30. `sec_verify.tex` 91: "the constant $\frac{88}{9}$" does not appear in Theorem 9.7's text, which writes "$<10\varepsilon$". Align the two.
31. `sec_verify.tex` 144–145: "A local law up to the boundary of a face is open". With Theorem 6.7 this is no longer accurate for facets of faces with at most three states. Say "up to lower-dimensional corners, and up to facets for faces with four or more states".

---

## 8. Questions for the author

1. **The observation model.** With calibrated killing, the survival probability $\sum_nP_N(n)e^{Tv\cdot n/N}$ decays like $e^{-T\lambda_V(v)}$ and gives all principal minors at once, by Lemma 9.9. Why is the modal support, with the exposure descent through all faces, the right observable? In what experimental or theoretical setting is the argmax-support available while the survival probability is not?
2. **The boundary layer for four or more states.** Can Lemma L be proved for $|G|\ge3$ by writing out the complex-phase version of Lemma B.1 sketched at lines 434–456? If not, would you agree to state Theorem 6.7 only for $|F|\le3$ and record the general case as a conjecture?
3. **Novelty of Part IV.** Which of Proposition 10.3, Lemmas 10.10 and 10.12, and Theorem 10.14 go beyond Wentzell (1972), Freidlin–Wentzell, Chapter 6, Catoni (1999), Olivieri–Vares, Chapter 6, and Trouvé (1996)? And exactly which statement of Catoni gives the exit-time asymptotics from a general domain used in Theorem 10.1?
