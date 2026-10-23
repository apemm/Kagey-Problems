# Paper C: independent referee audit of the core mathematics

All manuscript line citations below open the preserved audited copies in `evidence/01_C/sources/`. Their original workspace paths and SHA-256 hashes are in the manifest. Concurrent exposition edits changed `sec_model.tex`, `sec_intro.tex`, and `sec_complete.tex` after the snapshots; I inspected those differences and found no change to the audited core theorem statements or proofs. The observed differences are preserved in [the concurrent-change record](<evidence/01_C/concurrent_source_changes.json>).

## 1. Ranked actionable findings

### Takeaway

I found no theorem-invalidating defect in the audited chain of arguments for first-order global support selection, the irreducible-face local law, face maxima, crossings, or the stated weak-field and next-order results. There is one concrete scope error in the probabilistic explanation of the rate function, and one optional precision improvement concerning the displacement of the maximizing composition. These should not be reported as failures of the global-selection theorem: that theorem has the necessary hypotheses. The proof audit and its limits are documented below, with source snapshots in [the evidence manifest](<evidence/01_C/source_manifest.json>).

### Cited Findings

#### 1. [P2, localized mathematical scope correction] Restrict the probability interpretation of the variational functional

**Location.** `sec_firstorder.tex:166–177`, particularly lines 173–177, immediately before `\label{prop:rate}`. The functional is introduced for a general face, and the prose says that the chance of remaining in the face with occupation fractions near alpha decays like `exp(-T I_F(alpha))`. The cited result, `\label{thm:first}`(i), actually assumes (H). This unrestricted probabilistic interpretation is false for general reducible faces and starts. [Definition and interpretation](<evidence/01_C/sources/sec_firstorder.tex#L166>); [actual theorem hypotheses](<evidence/01_C/sources/sec_firstorder.tex#L385>).

**Concrete counterexample.** Take

\[
 Q=\begin{pmatrix}-2&1&1\\0&0&0\\0&0&0\end{pmatrix},\qquad
 \mu=\delta_1,\qquad F=\{1,2,3\}.
\]

The variational definition gives

\[
 I_F(\alpha)=\sup_{u>0}\alpha_1\left(2-\frac{u_2+u_3}{u_1}\right)=2\alpha_1.
\]

At `alpha=(1/3,1/3,1/3)` this is `2/3`, finite. Nevertheless a path is absorbed at either state 2 or state 3 after its first jump, so it cannot have fractions in a sufficiently small neighborhood of that alpha. The probability is identically zero, in both continuous and discrete time. This is an analytic counterexample; a separate exact rational path calculation also gives `P_9(3,3,3)=0` at `h=1/10`. [Variational definition](<evidence/01_C/sources/sec_firstorder.tex#L169>); [independent calculation and explanation](<evidence/01_C/independent_checks.json>).

**Minimal repair.** Restrict the probabilistic interpretation in lines 173–177: “For a face satisfying (H), this is the occupation-time rate of the chain killed on leaving F; Theorem ... gives its local form away from the boundary.” Keep the variational definition on arbitrary faces, its lower bound by lambda, and the reducible first-order bounds. Nothing in `thm:first` needs alteration. The example face is not admissible, exactly as `lem:admissible` predicts; that distinction is already respected by the formal selection theorem. [Admissibility criterion](<evidence/01_C/sources/sec_model.tex#L118>); [selection theorem](<evidence/01_C/sources/sec_firstorder.tex#L395>).

#### 2. [P3, optional precision] Describe the next-order displacement as a quadratic-model displacement unless its smaller-error regime is stated

**Location.** `sec_secondorder.tex:804–809`, especially line 807: the best composition “moves by about” `N Sigma_F gamma_F / T`. The formal location theorem proves only `alpha_hat-alpha*=O(1/T)` over the full range `T<=N^(1/3)`. The supplement computes the quadratic-model center and proves the maximum-value expansion; it does not state a uniform asymptotic equivalence for the actual displacement throughout that range. [Explanatory sentence](<evidence/01_C/sources/sec_secondorder.tex#L804>); [formal location bound](<evidence/01_C/sources/sec_secondorder.tex#L308>); [quadratic model and rounding](<evidence/01_C/sources/supplement.tex#L805>).

**What the displayed estimates support.** Completing the square at the actual maximizer and comparing with the rounded model center yields, after enlarging the fixed local ball constants,

\[
 \widehat\alpha'-\alpha^{*\prime}
 =\frac{\Sigma_F\gamma_F}{T}
 +O\!\left(T^{-3/2}+\sqrt{T/N}\right).
\]

Indeed the objective error is `O(T^-2+T^2/N)` and the quadratic loss is of order `T |x-Sigma gamma/T|^2`. Thus the error is `o(1/T)` when `T -> infinity` and `T^3/N -> 0`, including `T asymp log N`. At the endpoint `T=N^(1/3)`, this reasoning only gives an error of the same order as `1/T`. This is a deduction from the audited estimates, not a counterexample to the claimed maximum-value formula. [Local objective expansion](<evidence/01_C/sources/supplement.tex#L786>); [completed square](<evidence/01_C/sources/supplement.tex#L807>); [rounded lower bound](<evidence/01_C/sources/supplement.tex#L828>).

**Minimal repair.** Say “the quadratic model moves by ...”, or connect the actual leading displacement explicitly to the condition `T^3/N -> 0` already stated in line 822 for resolution of the next coefficient. This is an exposition recommendation, not a requested theorem correction. [Existing resolution qualification](<evidence/01_C/sources/sec_secondorder.tex#L822>).

### Inferences

- The serious potential failure modes specified in the assignment are addressed by actual arguments in the present sources. In particular, the manuscript does not infer a global maximum from an interior LLT alone, and does not silently apply the Gaussian face prefactor to reducible faces. The source-level checks supporting this conclusion are in Section 2 below. [Whole-face exclusion](<evidence/01_C/sources/sec_secondorder.tex#L263>); [reducible bounds](<evidence/01_C/sources/app_torus.tex#L486>).
- The first finding concerns the interpretation of a functional outside the formal theorem's scope. The branching counterexample does **not** disprove the first-order theorem, its arbitrary-start claim, or the irreducible local law. [Theorem hypotheses](<evidence/01_C/sources/sec_firstorder.tex#L385>).

### Gaps

- No current counterexample to the audited formal core results was found. This is a referee assessment of the inspected proof chain, not an exhaustive certification of the merged paper. Explicit exclusions and dependence on companion-paper inputs appear in Section 3.

## 2. Audit of the proof chain and its hypotheses

### Takeaway

The central mechanism is sound on inspection: admissible component paths give the correct power of N for every start; a separate positive-coefficient contour bound controls entire faces; Perron perturbation gives a nondegenerate saddle without reversibility; and the discrete-continuum comparison is a **relative** `O(T^2/N)` estimate. At `T asymp log N` this error is smaller than both the `1/T` correction and the `1/T^2` remainder. [First-order bounds](<evidence/01_C/sources/sec_firstorder.tex#L395>); [upper bound](<evidence/01_C/sources/sec_firstorder.tex#L363>); [relative comparison](<evidence/01_C/sources/sec_secondorder.tex#L207>).

### Cited Findings

#### A. Definitions, arbitrary starts, and admissibility — checked

**Locations.** `sec_model.tex:9–39`, `def:faces` at 47–59, and `lem:admissible` at 118–157. The observations are `X_1,...,X_N`, giving N visits and N-1 transitions. `Q_F` retains the full exit rates on its diagonal, so it is the killed generator. Admissibility requires an actual path starting in `supp(mu)` and using exactly F. [Model](<evidence/01_C/sources/sec_model.tex#L9>); [faces](<evidence/01_C/sources/sec_model.tex#L47>).

The condensation graph is acyclic. A path cannot return to a component it has left, so a path covering F must traverse all components once in an order with an edge between successive components and positive initial mass in the first one. Conversely, strong connectivity supplies a covering walk between prescribed entry and exit states in each component. This proves the stated criterion; mere reachability of each state from the start, or `mu(F)>0`, would not suffice. The branching example in Finding 1 has both properties but cannot cover F. [Both directions of the proof](<evidence/01_C/sources/sec_model.tex#L128>).

For an irreducible face, admissibility is exactly `mu(F)>0`; this does **not** require positive mass at every state of F. With symmetric support no edges connect distinct strongly connected components, so every admissible face is irreducible. With full-support mu, a reducible F is dominated in the first-order objective by a component C with `lambda_C=lambda_F` and fewer states; C is then admissible. These are sufficient conditions for irreducibility of the selected faces, and the manuscript uses them as such. [Admissibility parts (b),(c)](<evidence/01_C/sources/sec_model.tex#L153>); [`thm:hull`(c), proof](<evidence/01_C/sources/sec_firstorder.tex#L565>).

#### B. Exact run law and continuum measure — checked

**Locations.** `lem:runs`, `sec_model.tex:168–195`; `lem:continuum`, 211–269. A word with M runs has M-1 switches and `n_i-m_i` stays at state i. Splitting the n_i visits into m_i positive run lengths gives `binom(n_i-1,m_i-1)`. The continuum free holding times have simplex volumes `t_i^(m_i-1)/(m_i-1)!`. Using any k-1 occupation coordinates changes the chosen coordinate measure by determinant of absolute value 1. Consequently the lattice-cell factor is `N^-(k-1)`, with no additional square-root-of-k factor. [Discrete law](<evidence/01_C/sources/sec_model.tex#L174>); [continuum change of variables](<evidence/01_C/sources/sec_model.tex#L247>).

The continuum event includes visiting every state of F. Words missing a state disappear in the contour inversion, rather than becoming spurious terms in the interior density. This deals with the singular occupation laws on smaller faces. [Event definition](<evidence/01_C/sources/sec_model.tex#L211>); [Cauchy elimination of missing-state words](<evidence/01_C/sources/app_torus.tex#L188>).

#### C. Variational rate and boundary separation — checked under the stated irreducibility hypotheses

**Locations.** `prop:rate`, `sec_firstorder.tex:186–334`. Writing `u=exp(psi)` gives the correct concave optimization. Strong connectivity and positive interior alpha make the objective coercive modulo constants. The stationary-law criterion proves uniqueness of its maximizer modulo scaling and strict convexity in alpha. The resolvent argument supplies `I_G>=lambda_G` even when a subface G is reducible. Sending the off-subface coordinates of u to zero proves `I_F=I_G` on the subface; strict Perron monotonicity for a proper principal submatrix of the irreducible matrix on F then gives the boundary gap. I found no missing reversibility assumption in these steps. [Coercivity and uniqueness](<evidence/01_C/sources/sec_firstorder.tex#L262>); [general-face resolvent bound](<evidence/01_C/sources/sec_firstorder.tex#L238>); [boundary identity and strict gap](<evidence/01_C/sources/sec_firstorder.tex#L299>).

The reversible square-root expression is correctly stated as an equality only under detailed balance. The later flow identity explains its discrepancy for nonreversible faces. It should not be substituted as an equality into a directed example. [Reversible hypothesis](<evidence/01_C/sources/sec_firstorder.tex#L196>); [flow discrepancy](<evidence/01_C/sources/sec_secondorder.tex#L674>).

#### D. Whole-face upper bound and global exclusion — checked; no interior-LLT gap found

**Locations.** `lem:upper`, `sec_firstorder.tex:363–378`; its proof in `app_torus.tex:226–285`; `thm:facemax` outside-U step at `sec_secondorder.tex:263–276`. The proof retains the crucial `h^(k-1)` factor and works for any positive composition, including counts of size 1. It majorizes the run law by `H_sigma`, with `sigma=exp(h q_max)`, and uses the contour at radii `sigma theta`. The scaling identities for X, g and b give the exponent error `O(h^2 |n|)`. At `|n|=N` and `T<=N^(1/3)`, this error is bounded and can be absorbed into a fixed constant. [Positive-term majorization](<evidence/01_C/sources/app_torus.tex#L245>); [scaled contour estimate](<evidence/01_C/sources/app_torus.tex#L260>).

For a fixed ball U about `alpha*`, lower semicontinuity and the unique minimizer give a positive rate gap on the compact set `Delta_F \ U^o`. Each point of that set has a linear variational witness strictly exceeding lambda; a finite subcover yields finitely many fixed theta vectors. Applying `lem:upper` with the appropriate witness gives

\[
 P_N(n)\le C(T/N)^{k-1}e^{-T(\lambda_F+2\eta)}.
\]

Relative to the proposed face maximum this is `O(T^((k-1)/2) exp(-2 eta T))`. This argument includes sequences of compositions approaching the boundary and does not require uniform extension of the interior LLT there. [Finite-cover construction and exclusion](<evidence/01_C/sources/sec_secondorder.tex#L263>).

#### E. Reducible faces and arbitrary-start global selection — checked

**Locations.** `thm:first`(ii)–(iv), `sec_firstorder.tex:395–470`; full bounds in `app_torus.tex:486–587`. For a **fixed composition** the total number of visits to each component fixes its block length. Hence the upper-bound multiplication over components needs no summation over possible residence times and incurs no missing factor of N. The finitely many patterns fix initial state, component order and intercomponent transitions; start-state versions of `lem:upper` bound the blocks. Internal factors `h^(|C|-1)` and the r-1 intercomponent switches multiply to exactly `h^(|F|-1)`. [Fixed lengths and patterns](<evidence/01_C/sources/app_torus.tex#L513>).

For the lower bound, `m=ceil(N/T)` visits give physical duration of order 1 in each short component, with a positive probability of a prescribed covering tour between any entry and exit states. The component of minimum exit rate and least such size k* receives the remaining visits. A positive Perron vector bounds its survival and the two short tours enforce its endpoints. Dividing this family's probability by its possible compositions gives exactly

\[
 cN^{-(|F|-1)}T^{|F|-k^*}e^{-T\lambda_F}
 \le M_F\le
 CN^{-(|F|-1)}T^{|F|-1}e^{-T\lambda_F}.
\]

The accounting of visits versus transitions in Claim B is consistent: `(m-1)+(ell-2m+1)+(m-1)=ell-1`. Equal component exit rates, including a possible polynomial survival factor from a reducible block structure, do not invalidate these composition bounds. The proof makes no assumption that mu charges the long-lived component. [Short tours](<evidence/01_C/sources/app_torus.tex#L544>); [long block](<evidence/01_C/sources/app_torus.tex#L557>); [composition count](<evidence/01_C/sources/app_torus.tex#L572>).

Putting `T=tau log N` into these bounds gives the same power `N^-Phi_tau(F)` for every admissible face; the remaining logarithmic factors cannot overcome a fixed gap between the finitely many face exponents. Thus every sufficiently large-N global mode has a minimizing support. Location at `alpha*` is asserted only when the minimizing faces are irreducible. [Finite-face comparison](<evidence/01_C/sources/sec_firstorder.tex#L457>).

#### F. Perron perturbation, nondegeneracy, and the torus saddle — checked

**Locations.** `lem:perron`, `app_torus.tex:29–70`; `prop:constant`(a), proof at 80–127; local-law saddle at 303–398. Differentiating the simple Perron eigenvalue gives `grad kappa=pi` and `Hess kappa=DZ+Z^T D`. With `u=Z eta`, the quadratic form is

\[
 \eta^T\Gamma\eta=\sum_{i\ne j}\pi_iG_{ij}(u_i-u_j)^2.
\]

Strong connectivity forces the kernel to consist exactly of constant vectors, without detailed balance. Deleting one coordinate therefore gives a positive definite Sigma. The constrained Perron-gradient inverse then yields `Hess I=Sigma^-1`; the proof does not rely on strict convexity alone to infer a positive definite Hessian. [Dirichlet-form calculation](<evidence/01_C/sources/app_torus.tex#L59>); [inverse-gradient argument](<evidence/01_C/sources/app_torus.tex#L96>).

The deleted generator need not be irreducible. Its Perron root is strictly negative at the chosen radii, so its resolvent has an absolutely convergent positive-coefficient series. The real saddle is unique on the torus because the loss in real part includes `sum_(i>=2) alpha_i theta_i(1-cos phi_i)`, with all coefficients positive. Thus a directed cycle does not create an extra saddle through the period of its embedded jump chain. The Hessian determinant conversion is `det H=det Sigma/alpha_1^2`, and the amplitude identity is `alpha_1 b(theta')=(mu.r)(l.1)`; these cancel correctly to give C_F. [Resolvent construction](<evidence/01_C/sources/app_torus.tex#L145>); [strict torus maximum](<evidence/01_C/sources/app_torus.tex#L303>); [Hessian conversion](<evidence/01_C/sources/app_torus.tex#L332>); [amplitude cancellation](<evidence/01_C/sources/app_torus.tex#L375>).

For the precise literature comparison, I checked Hervé–Ledoux, Proposition 3.1: their occupation-time application assumes irreducibility of the generator and each one-state-deleted subgenerator. Paper C's own contour proof avoids needing that extra assumption. I did not substitute that published theorem for Paper C's relative tilted estimate. [Primary paper, Proposition 3.1](https://arxiv.org/html/1306.5353v1#S3); [Paper C comparison](<evidence/01_C/sources/sec_intro.tex#L321>).

#### G. Relative discretization and the logarithmic regime — checked

**Locations.** `lem:discrete`, `sec_secondorder.tex:207–211`; proof in `app_torus.tex:411–484`. The ratio of each discrete run term to the corresponding continuum term is kappa_m. The lower bound uses the binomial product and `log(1-x)>=-x-x^2`; terms with excessive runs are zero and do not invalidate the bound. For the upper bound, the continuum run-count generating function is `H_(exp c)/H`. The contour upper bound and the continuum local lower bound give `log E exp(M-1)<=C T`, and hence both `E M^2=O(T^2)` and `E exp(h q_max M)=1+O(T^2/N)`. This supplies relative rather than additive control, even for very small point probabilities. [Term ratio and truncation](<evidence/01_C/sources/app_torus.tex#L411>); [moment estimates](<evidence/01_C/sources/app_torus.tex#L450>).

The use of the continuum LLT in this comparison is not circular: that LLT was proved by the contour and Laplace arguments before any discrete approximation. At `T asymp L=log N`, `T^2/N=O(L^2/N)=o(L^-m)` for every fixed m. At the wider endpoint `T=N^(1/3)`, the same error is only `1/T`; the text correctly uses that endpoint for an O(1/T) location estimate and explicitly notes the stricter condition for resolving the next coefficient. [Continuum proof completion](<evidence/01_C/sources/app_torus.tex#L394>); [use of the one-third exponent](<evidence/01_C/sources/sec_secondorder.tex#L315>); [resolution condition](<evidence/01_C/sources/sec_secondorder.tex#L822>).

#### H. Face maxima, crossings and tie windows — checked

**Locations.** `thm:facemax`, `sec_secondorder.tex:219–321`; `thm:crossing`, 329–375; `thm:window`, 391–509. Once the whole-face bound excludes the complement of U, the local quadratic rate and linear log-amplitude term give the stated maximum and location. A lattice point next to `alpha*` costs only `O(1/N+T/N^2)`, within the claimed error. The bounded-T extension uses positivity and compactness to bound ratios above and below, which is sufficient for the logarithmic statement even when a relative O(1/T) term is not small. [Local optimization and rounding](<evidence/01_C/sources/sec_secondorder.tex#L279>); [bounded T](<evidence/01_C/sources/sec_secondorder.tex#L300>).

For crossings, continuity of the maximum of finitely many positive polynomials gives existence. The comparison function `delta T+(Delta/2) log T` has derivative at least delta. First locating every root at order L makes the error O(1/L), and bounds all such roots within O(1/L) of one deterministic value. This does not prove uniqueness of the actual crossing; the manuscript explicitly says so. [Root localization](<evidence/01_C/sources/sec_secondorder.tex#L349>); [explicit nonuniqueness qualification](<evidence/01_C/sources/sec_secondorder.tex#L381>).

The tie-window theorem expressly requires every first-order minimizing face to be irreducible. Its exclusion of other faces follows from a uniform exponent gap near tau*, while the tied-face calculation retains the `((k-1)/2) log(1+y)` term for the wider `|t|<=epsilon L` range. That term is needed there and is present. Coincident lines are correctly left unresolved. [Hypothesis and qualification](<evidence/01_C/sources/sec_secondorder.tex#L391>); [uniform window formula](<evidence/01_C/sources/sec_secondorder.tex#L438>); [wide-window comparison](<evidence/01_C/sources/sec_secondorder.tex#L468>).

The directed 3-cycle is a genuine demonstration of the restriction: with rates `(b,1,1)`, `b>2`, and start at state 1, the reducible pair maximum is exactly `b h (1-h)^(N-2)` at `(1,N-1,0)`. Its `T^1` prefactor changes the first crossing's bracket coefficient of log log N to 1 and the second to 0. The supplement also supplies a continuity/sign argument giving existence of the second crossing. I checked these comparisons, including the small-T full-face upper bound and the role of `b>2`. [Statement and exact pair](<evidence/01_C/sources/sec_secondorder.tex#L722>); [full comparisons](<evidence/01_C/sources/supplement.tex#L563>); [independent N=9 exact support check](<evidence/01_C/independent_checks.json>).

#### I. Constants, directed trees, and a nonuniform-start check — checked

**Locations.** `def:tilt`, `sec_secondorder.tex:28–71`; `prop:constant`, 78–150; `prop:forest`, 521–625; `lem:forest`, `app_torus.tex:603–700`. The factor `(mu.r)(l.1)` is invariant under the allowed reciprocal rescaling of r and l and is positive exactly when `mu(F)>0`. The group inverse, the stationary flow balance, the adjugate factorization and the directed tree normalization give the stated determinant. The reversible reduction has the expected `2^(k-1)` factor. No reversibility is tacitly needed for the general tree formula. [Definitions](<evidence/01_C/sources/sec_secondorder.tex#L28>); [general forest proof](<evidence/01_C/sources/app_torus.tex#L641>).

Small independent rational calculations compared direct group-inverse covariance determinants with explicit rooted-tree enumeration. They agree for rates `(2,3)` on a pair (`12/125`), the directed `(3,1,1)` cycle (`27/2401`), and a nonreversible three-state generator with rows `(-3,2,1)`, `(1,-4,3)`, `(4,2,-6)` (`2399/777924`). These are sanity checks, not substitutes for the audited algebra. [Independent script](<evidence/01_C/independent_checks.py>); [exact outputs](<evidence/01_C/independent_checks.json>).

A useful additional hand check shows why the equal-start hypothesis in `prop:nextterm`(iv) must remain. For symmetric pair rates a, common full exit q, and start masses `m=mu_i`, `n=mu_j`, with `m+n>0`, the center saddle has

\[
 \Psi=a\cos\varphi,\quad
 \chi=a\{m e^{i\varphi}+(m+n)+n e^{-i\varphi}\}.
\]

Thus `c(alpha*)=-1/(8a)`, `gamma=(n-m)/(m+n)` in the alpha_j coordinate, and `Sigma=1/(4a)`. The **face-maximum** coefficient is therefore

\[
 c_F=-\frac1{8a}+\frac1{8a}\left(\frac{n-m}{m+n}\right)^2
 =-\frac{mn}{2a(m+n)^2}.
\]

In particular it is zero for a deterministic start, not `-1/(8a)`. This is consistent with the general maximum-shift correction and with the restricted symmetric-start special case; it is not a counterexample to the proposition as stated. The derivation uses the one-dimensional resolvent directly, then the audited Wick coefficient. [Pair resolvent template](<evidence/01_C/sources/supplement.tex#L897>); [general coefficient and shift](<evidence/01_C/sources/sec_secondorder.tex#L776>); [exact rational coefficient checks](<evidence/01_C/independent_checks.json>).

#### J. Laplace lemma and the next term — checked at proof level

**Locations.** `lem:laplace`, `app_laplace.tex:10–108`; `lem:laplace2` and `eq:laplace-c1`, 115–139; supplement `supp:laplace-next`, 606–716, and `supp:nextterm`, 718–1017. Compactness gives uniform spectral and off-saddle gaps. The basic lemma's fourth phase derivatives and second amplitude derivatives suffice for the O(1/T) remainder after cancellation of odd terms. For the next lemma, bounded sixth/fourth derivatives suffice to expand through the odd `T^-3/2` term with integrated O(T^-2) remainder. The supplement supplies actual integrable remainder bounds, rather than only a formal Taylor series. [Basic remainder](<evidence/01_C/sources/app_laplace.tex#L81>); [higher remainder](<evidence/01_C/sources/supplement.tex#L636>).

I checked the Wick contraction coefficients: `1/2` for the second amplitude derivative; `1/2` for the amplitude/phase-cubic term; `1/8` for the phase quartic; and `1/12`, `1/8` for the two classes of cubic-squared pairings (six and nine pairings, respectively). Complex derivatives carry their own signs. The coefficient is real and independent of the eliminated state because it is recovered from the real density's asymptotic expansion. [Formula](<evidence/01_C/sources/app_laplace.tex#L123>); [pairing count](<evidence/01_C/sources/supplement.tex#L702>); [reality and coordinate independence](<evidence/01_C/sources/supplement.tex#L729>).

The maximization adds `+(1/2) gamma^T Sigma gamma` to `c(alpha*)`, with the correct sign. Rounding the quadratic center loses `O(T/N^2)`, absorbed in the displayed remainder. In the next crossing equation, multiplying the logarithmic difference by T gives error `O(1/T+T^3/N)`, hence O(1/L) at `T asymp L`; the sign `c_F-c_G` in `eq:crossingnext` is correct. [Maximum-value proof](<evidence/01_C/sources/supplement.tex#L759>); [crossing sign and remainder](<evidence/01_C/sources/supplement.tex#L844>).

For the symmetric pair, the independent Bessel route gives `-1/(8a)`. I checked the external expansion precisely: DLMF 10.40.1 and 10.17.1 give corrections `+1/(8z)` for I_0 and `-3/(8z)` for I_1, so their sum has relative correction `-1/(8z)`. The supplement's bounded-z extension and the replacement `z=aT/(1-qh)` introduce only the stated `O(T^2/N)` error. This check still depends on the companion Paper A finite-N Bessel bound; that bound was not re-proved in this audit. [Primary Bessel expansion](https://dlmf.nist.gov/10.40.E1); [primary coefficient formula](https://dlmf.nist.gov/10.17.E1); [Paper C comparison](<evidence/01_C/sources/supplement.tex#L857>).

For the complete graph with mu constant on F, I checked the closed contour integrand, its Taylor coefficient structure, the exchangeable-Gaussian moment reduction, and the final cancellation to `c_F=-(k-1)/8`. The local symmetry makes gamma zero; it is not legitimate to carry that last coefficient over unchanged to arbitrary starts. The moment formulas use the Gaussian in the sum-zero hyperplane, `W_2` with k-1 chi-square degrees of freedom, and `E W_3^2=6(k-1)(k-2)/k`, consistently with the pair case. This was a hand audit of the presented calculation, not a separate computer-algebra derivation in every dimension. [All-size calculation](<evidence/01_C/sources/supplement.tex#L911>); [moments and cancellation](<evidence/01_C/sources/supplement.tex#L980>).

#### K. Weak fields and normalization — checked

**Locations.** `prop:weakfield`, `sec_secondorder.tex:862–945`; selected complete-graph consequences at `sec_complete.tex:379–438,485–513`. For a fixed field vector in a compact set the factor `exp(xi.alpha)` is bounded above and below. It cannot change the power of N in the first-order comparison. In the face-max proof it changes the log-amplitude gradient to `gamma+(xi_i-xi_1)_(i>=2)`, preserving localization and the required uniform constants. The singleton statement is exact. [Hypotheses and statement](<evidence/01_C/sources/sec_secondorder.tex#L862>); [gradient change and localization](<evidence/01_C/sources/sec_secondorder.tex#L898>).

The tie-window extension correctly repeats the requirement that all minimizing faces be irreducible. It shifts log K by the average field at the quasi-ergodic law, using unnormalized face weights; the common partition function cannot change which composition is a mode. The normalization limit `Z -> exp(xi.pi)` assumes the full generator is irreducible, and its proof controls total probability outside a neighborhood by multiplying pointwise bounds by the number of compositions. This works for any `T -> infinity` in the stated range, without an additional comparison between log N and T. [Window argument](<evidence/01_C/sources/sec_secondorder.tex#L923>); [normalization argument](<evidence/01_C/sources/sec_secondorder.tex#L933>).

The complete-graph phase corollary selects a limiting-score maximizing support for fixed `(t,xi)` and explicitly warns that equality of scores need not give both finite-N modes. Sorted fields select the top-k states at a fixed size. The proposed quadratic field hierarchy follows because the second differences of log D_k are at most 1/2 and `2H/3>1/2`. I checked these short algebraic consequences; they do not require a uniform result for fields growing with N. [Phase corollary and tie qualification](<evidence/01_C/sources/sec_complete.tex#L379>); [hierarchy argument](<evidence/01_C/sources/sec_complete.tex#L485>).

### Inferences

- The arbitrary-start theorem and the half-log-log crossing result have different scopes, correctly distinguished in their statements. Any exposition edit must preserve admissibility for the former and (H), or irreducibility of all tied faces, for the latter. The directed-cycle example and the branching counterexample illustrate two different obstructions. [First-order theorem](<evidence/01_C/sources/sec_firstorder.tex#L385>); [crossing and tie hypotheses](<evidence/01_C/sources/sec_secondorder.tex#L329>).
- Positive start mass on a face is enough for a positive LLT constant; full support of the start is not needed there. Full support is used elsewhere as a sufficient way to eliminate reducible first-order winners. These conditions should not be conflated. [Constant positivity](<evidence/01_C/sources/app_torus.tex#L394>); [full-support domination](<evidence/01_C/sources/sec_firstorder.tex#L565>).

### Gaps

- General crossing uniqueness and finer distinctions between coincident tie-window lines remain unresolved by these arguments, and are already excluded from the manuscript's claims. I did not find grounds to strengthen either conclusion. [Crossing limitation](<evidence/01_C/sources/sec_secondorder.tex#L381>); [coincident-line limitation](<evidence/01_C/sources/sec_secondorder.tex#L413>).
- There is no general Gaussian prefactor or universal log-log coefficient for reducible faces in the audited theory. The first-order upper/lower bounds and the explicit cycle example are what have been checked, not a complete second-order reducible theory. [Stated reducible limitation](<evidence/01_C/sources/sec_firstorder.tex#L473>).

## 3. Coverage, evidence, and explicit unaudited portions

### Takeaway

This was a fresh source-based audit on 2026-10-22. I read the requested researcher instructions first and did not consult the earlier Paper C report or its conclusions. No manuscript was edited, and no Lean/Lake build or long computation was run. The only executable checks were small, exact, standard-library calculations; the check command finished in approximately half a second. Source hashes and copies preserve the version behind the line references. [Manifest](<evidence/01_C/source_manifest.json>); [check script](<evidence/01_C/independent_checks.py>).

### Cited Findings

- **Read in full, with core proof audit:** `sec_model.tex` (298 lines), `sec_firstorder.tex` (598), `sec_secondorder.tex` (946), `app_torus.tex` (700), and `app_laplace.tex` (158). The source manifest records their exact SHA-256 hashes and snapshots. [Manifest](<evidence/01_C/source_manifest.json>).
- **Supplement read in full:** 1,029 lines. Sections S2–S4, `supp:threecycle`, `supp:laplace-next`, and `supp:nextterm`, received the detailed audit described above. S1's path/two-triangle applications were read for context, but their entire spectral/hull classifications and resultant identities were not independently re-proved. Those computations are explicitly identified in the supplement. [Supplement S2](<evidence/01_C/sources/supplement.tex#L493>); [S1 computational dependencies](<evidence/01_C/sources/supplement.tex#L473>).
- **Selected additional material:** the introduction's main theorem statements and precise LLT comparison, the exact pair identity, and the complete-graph start/weak-field corollaries used above. This does not constitute a complete audit of all material imported from Paper B. [Introductory scope](<evidence/01_C/sources/sec_intro.tex#L78>); [pair identity](<evidence/01_C/sources/sec_complete.tex#L15>); [start corollary](<evidence/01_C/sources/sec_complete.tex#L270>).
- **Independent evidence:** the exact branching counterexample, exact directed-cycle support/mode check, three rational covariance/tree comparisons, and the symmetric pair's start-dependent next coefficient are recorded in [the JSON outputs](<evidence/01_C/independent_checks.json>). The code imports no manuscript verification scripts.
- **Internet use was narrow:** Hervé–Ledoux Proposition 3.1 was consulted to check the deleted-subgenerator hypothesis precisely; DLMF was consulted for the sign and normalization of the Bessel correction. No broad novelty search, journal-guideline search, or redundant literature survey was performed. [Primary LLT paper](https://arxiv.org/html/1306.5353v1#S3); [DLMF expansion](https://dlmf.nist.gov/10.40.E1); [DLMF coefficients](https://dlmf.nist.gov/10.17.E1).

### Inferences

- For the parent's immediate C exposition pass, the concrete repair is the qualification of the rate interpretation in Finding 1. Finding 2 is an optional way to avoid suggesting a stronger uniform location expansion than the displayed estimates supply. The remainder of the core audit supports keeping the formal statements and their existing hypotheses. [Relevant interpretation](<evidence/01_C/sources/sec_firstorder.tex#L173>); [relevant displacement wording](<evidence/01_C/sources/sec_secondorder.tex#L804>).
- No result here certifies the current PDF or a source version edited after the snapshots. Use the named labels and preserved snapshots if line numbers drift during the parent's edits. [Snapshot manifest](<evidence/01_C/source_manifest.json>).

### Gaps

- **Not independently audited:** the full finite-N complete-graph balancing/insertion arguments and all claims in `app_complete.tex`; the rare-count/vertex Laguerre theory in `sec_vertex.tex` and `app_vertex.tex`; the full catalog of examples and numerical figures in `sec_examples.tex`; verification scripts, Lean statements/proofs, extraction of computational claims, build reproducibility, and PDF rendering. These remain outside this core-probability assignment.
- **Companion-paper inputs not re-proved:** Paper A's finite-N Bessel inequality and coefficientwise balancing result used for the independent symmetric-pair route; Paper B's entire imported finite-N development. The general contour/Laplace proof of the core local law does not rely on the Bessel check. [Cited pair dependencies](<evidence/01_C/sources/sec_complete.tex#L33>); [Bessel input](<evidence/01_C/sources/sec_model.tex#L99>); [independent general contour route](<evidence/01_C/sources/app_torus.tex#L287>).
- **No uniformity beyond the stated setting:** Q, mu, dimension and faces are fixed. This audit supplies no result for vanishing start masses, rates approaching reducibility, dimensions growing with N, compacts approaching a face boundary, or fields growing with N. The stated convention and field hypotheses are essential to the uniform constants. [Fixed-data convention](<evidence/01_C/sources/sec_model.tex#L106>); [compact-field hypothesis](<evidence/01_C/sources/sec_secondorder.tex#L862>).
- **Not an EJP acceptance or novelty verdict:** the note audits mathematical validity within the coverage above. It does not establish that the complete merged manuscript is ready for submission, that every reference is accurate, or that all claimed contributions are new.
