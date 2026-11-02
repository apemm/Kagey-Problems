# First-step bias and the number of modes

## Can the finite shape theorem hold for every first-step bias?

### Takeaway

The second-difference argument does not extend with its original orientation. A first-difference argument gives a stronger conclusion: for every initial bias `q` in `[0,1]`, every `0 < epsilon < 1`, and every time `n >= 1`, the mass function has at most two modal plateaus. This includes modes at either endpoint. The actual finite-law theorem and its arbitrary-interval increment form have passed `lake build PaperD.BiasedModes`; numerical checks are supplementary.

### Cited Findings

Guérin, Laulin, Raschel and Simon prove unimodality for a fixed first step and conjecture a centered interval of biases giving bimodality for each superdiffusive memory parameter. Their Remark 2.1(b) is the direct comparison: [arXiv full text](https://arxiv.org/html/2409.06836v1), [published article](https://doi.org/10.1214/25-EJP1362). Read in this investigation: introduction and Section 2, including the finite unimodality proof and bias conjecture. Sections 3 onward have not yet been read in full in this investigation.

Trinas and Valle's uniform local limit theorem applies to every initial bias. Their shape conclusions subsequently restrict to the fixed-start case. See Theorem 3.1 and the opening of Section 4: [full text](https://arxiv.org/html/2609.14753v1). **Read in this investigation: the full mathematical text, Sections 1–5 and references.** Their numerical certificates were read as described, not independently rerun.

### Inferences

Write `a = 1 - 2 epsilon`, `p = 1 - epsilon`, and let `P_t(k)` be the probability of `k` positive steps at time `t`, with `P_1 = (1-q,q)`. Put

\[
r_t(k)=\epsilon+ak/t,\qquad d_t(k)=P_t(k+1)-P_t(k).
\]

For `1 <= k <= t-1`, direct subtraction of the forward equations gives

\[
d_{t+1}(k)=r_t(k-1)d_t(k-1)+[1-r_t(k+1)]d_t(k).
\]

Both coefficients are at least `min(epsilon,1-epsilon)`. Indeed, `r_t(k)` is a convex combination of `epsilon` and `1-epsilon` on `0 <= k <= t`. This formula must not be used as a positive recurrence at either boundary.

For `q < 1`, define

\[
\xi_t=\frac{P_t(1)}{P_t(0)},\quad
b=\frac{a}{p}<1,\quad A=\frac\epsilon p>0.
\]

Since `P_t(0)=(1-q)p^{t-1}`, the boundary recursion is

\[
\xi_{t+1}=(1-b/t)\xi_t+A,\qquad \xi_1=q/(1-q).
\]

Writing `delta_t = xi_(t+1)-xi_t` gives the crucial identity

\[
\delta_{t+1}=\frac{t-b}{t+1}\delta_t+\frac{A}{t+1}.
\]

Consequently, a nonnegative increment is followed by a strictly positive increment. The sequence `xi_t` first decreases and then increases, allowing either part to be empty. Every strict horizontal sublevel set is an interval. Thus the left edge `l_t=d_t(0)` has sign pattern contained in `(+,-,+)`. When `q <= 1/2`, its initial value is nonpositive, and its pattern is contained in `(-,+)`.

Reflection gives `r_t=d_t(t-1)=-l_t(1-q)`. For `q <= 1/2`, its temporal pattern is contained in `(-,+,-)`. For fixed `N`, augment the interior row by future edge values:

\[
Z_t=(l_N,\ldots,l_{t+1},d_t(0),\ldots,d_t(t-1),r_{t+1},\ldots,r_N).
\]

At `t=1`, the reversed left history has pattern `(+,-)` and the right history has pattern `(-,+,-)`. They meet at `l_1=r_1=2q-1 <= 0`, so the whole initial pattern is contained in `(+,-,+,-)`. Every subsequent augmented row comes from nonnegative combinations of adjacent entries, with copied future boundary values. The interleaving lemma therefore preserves this oriented pattern. At `t=N`, it is exactly the first-difference row. Reflection and sign reversal leave `(+,-,+,-)` invariant, covering `q >= 1/2`. At `q=0`, the rightmost occupied bin is `t-1`, so `r_t=-P_t(t-1)<=0` and the same argument works without dividing by the reflected zero endpoint. Reflection covers `q=1`.

Finally, extending the mass function by zero adds the difference `P_N(0) >= 0` at the left and `-P_N(N) <= 0` at the right. These do not increase the pattern. There are at most two transitions from positive to negative, hence at most two modal plateaus. A modal plateau here is a maximal constant block bounded by a strict increase and a strict decrease; a flat stretch inside a monotone part is not counted as a separate mode.

The local limit theorem transfers any strict alternating pattern of increments in the limiting density back to sufficiently fine finite rows. Specifically, three local maxima at `x<y<z`, with no constant interval, yield `x<u<y<v<z` with `f(u)<min(f(x),f(y))` and `f(v)<min(f(y),f(z))`. Approximate these five points by ordered rescaled lattice points. Uniform local convergence preserves the four strict inequalities, contradicting the finite theorem. Therefore the analytic biased limit has at most two local maxima. This result does not by itself prove that the set of bimodal biases is a centered interval. That stronger part of the GLRS conjecture remains open in this investigation.

### Gaps

The finite theorem is kernel-checked in `kagey-problems/problem131/lean/PaperD/BiasedModes.lean`, using the actual existing conditional count law. Its two main declarations are `Kagey131.PaperD.BiasedModes.diff_no_pattern` and `no_four_increments`. Their only hypotheses are `0 < epsilon < 1`, `0 <= q <= 1`, and `n >= 1`. The namespace's `mass` is `q*fZ(epsilon,n,n-k)+(1-q)*fZ(epsilon,n,k)`, so no new abstract model or shape premise enters the conclusion. Transfer to the limit still needs the published uniform local limit theorem as an explicit external input or a separate smoothing proof. No complete bias-phase classification is claimed.

The stronger all-memory module passed `lake build PaperD.BiasedModes`. A focused `#print axioms` check of `diff_no_pattern`, `no_four_increments`, `mass_succ`, `ratio_succ`, and `increment_succ` reported only `propext`, `Classical.choice`, and `Quot.sound`. The ready-to-integrate mathematical proof is in `biased_modes_proof.tex` beside this note; it includes endpoint biases and the full boundary-history argument.

## What is the precise local-limit normalization?

### Takeaway

The lattice spacing is two for the walk position, so the density multiplier is `n^a/2`. The proposed floor embedding is correct and introduces an error smaller than `2 n^(-a)` in the spatial argument.

### Cited Findings

Trinas–Valle Theorem 3.1 states, for each fixed `a in (1/2,1)` and `q in [0,1]`,

\[
\sup_{j\in\mathbb Z:\ j\equiv n\pmod2}
\left|\frac{n^a}{2}\Pr(S_n=j)-f_{q,a}(j/n^a)\right|\longrightarrow0.
\]

Here `f_(q,a)` is the density of `S_n/n^a` in the limit, with first positive-step probability `q`. Their Section 3 interpolation uses mesh `2n^(-a)` and assigns value `(n^a/2) Pr(S_n=j)` at each lattice point. The full statement and proof were read in the [author manuscript](https://arxiv.org/html/2609.14753v1).

### Inferences

Set

\[
k_n(x)=\left\lfloor\frac{n+n^a x}{2}\right\rfloor,
\qquad j_n(x)=2k_n(x)-n,
\qquad x_n(x)=j_n(x)/n^a.
\]

Then `j_n(x)` has the required parity and

\[
0\le x-x_n(x)<2n^{-a}.
\]

The count law in `BiasedModes.mass` is `Pr(A_n=k)` with `S_n=2A_n-n`, so

\[
\frac{n^a}{2}\,\mathrm{mass}(\epsilon,q,n,k_n(x))
\longrightarrow f_{q,a}(x),\qquad a=1-2\epsilon.
\]

This follows by the displayed uniform lattice theorem and continuity of `f_(q,a)` at the fixed `x`. At any finitely many fixed ordered points `x_0<...<x_4`, the integer indices are eventually strictly ordered: the unrounded spacing is `(n^a/2)(x_(i+1)-x_i)`, which tends to infinity. Each fixed index also eventually lies between `0` and `n`, because `a<1`; the zero-extended formal law makes that support check unnecessary for applying the finite sign theorem. The positive multiplier `n^a/2` preserves all signs of differences. No extra factor of two, reflection, or Gamma normalization occurs.

### Gaps

This transfers shape using an existing fixed-parameter local limit theorem. It supplies no uniformity as `a` tends to one and must not be used as the missing uniformity step in the Landau peak-profile argument.

## Which tempting extensions are false?

### Takeaway

Exact rational counterexamples rule out two natural curvature extensions. They do not refute the first-difference theorem above.

### Cited Findings

These are calculations from the exact finite ERW recurrence, not claims taken from the literature.

### Inferences

At `a=9/10`, `q=199/200`, the temporal left-edge second difference `P_t(0)-2P_t(1)+P_t(2)` has signs `+,-,+,-,+` at `t=2,7,11,25,85`, respectively. All signs were checked using Python `fractions.Fraction`. The fair-start three-block temporal edge lemma therefore fails under arbitrary bias.

At `a=24/25`, `q=1/1200`, `N=80`, the spatial second differences have signs `-,+,-,+,-` at indices `1,2,74,75,77`. The values are approximately

\[
-0.00765633819,\quad 0.01078201972,\quad
-7.78767003\,10^{-9},\quad 1.54045917\,10^{-8},\quad
-5.56992414\,10^{-9}.
\]

Their signs were verified with exact rational arithmetic. The oriented five-block assertion `(+,-,+,-,+)` is false for biased starts, even though this counterexample still has only five blocks without the orientation requirement.

### Gaps

The unoriented five-block curvature conjecture was not settled. It is unnecessary for the first-difference route.

## What do the stress tests establish?

### Takeaway

The first-difference test checked every bias sign cell for a finite grid of memory parameters and times, with endpoint modes included. It found no third modal plateau.

### Cited Findings

The guarded run checked 182,364 bias cells across 54 memory parameters and selected times through `N=4000`. Parameters were 50 evenly spaced values of `a` from `0.01` to `0.99`, together with `0.985,0.995,0.999,0.9999`. Times were `2,3,4,5,6,8,10,15,20,30,40,60,80,100,150,200,300,500,750,1000,1500,2000,3000,4000`.

For each finite row, the first differences are affine in `q`. The code formed all roots in `[0,1]`, evaluated every open sign cell and both endpoints, and counted positive-to-negative transitions after deleting numerical zeros. It used the threshold `max(10^-12 times adjacent local mass, 10^-280)` to suppress floating-point roundoff and underflow. The largest observed pattern was `(+,-,+,-)`.

### Inferences

This is stronger numerical coverage in `q` than random sampling, but it remains floating-point evidence. In particular, the tolerance may erase tiny genuine features. A prior unguarded run produced a spurious third mode at a conditional endpoint bias because subnormal arithmetic generated alternating noise. That failure is why the exact proof, rather than the stress-test count, must support the theorem.

### Gaps

The reproducible script is now `probe_bias.py`, with output `probe_bias_results.json` in this directory. It reproduces all 182,364 cells and both exact rational counterexamples. A further diagnostic found no disconnected bimodal-bias sets on the tested grid; this is not a proof of a centered interval or of monotonicity in bias.

## How far is the novelty comparison resolved?

### Takeaway

The biased limit mode bound addresses a stated GLRS conjecture, but the finite theorem has an additional historical comparison that must be read before a first-priority claim is made.

### Cited Findings

- Drezner and Farnum, *A generalized binomial distribution* (1993), [publisher record](https://doi.org/10.1080/03610929308831202). The abstract describes dependent Bernoulli trials and both unimodal and bimodal examples. **Read: abstract and bibliographic record only.** The publisher PDF returned HTTP 403; no full text was found locally. An at-most-two theorem cannot be ruled in or out from the abstract.
- James, James and Qi, *Limit theorems for correlated Bernoulli random variables* (2008), Statistics and Probability Letters 78, 2339–2345, [author PDF](https://www.d.umn.edu/~yqi/mydownload/08letter.pdf), [DOI](https://doi.org/10.1016/j.spl.2008.01.104). **Read in full: all seven pages, including Sections 1–3, proofs and references.** It confirms the generalized-binomial recurrence with nonnegative dependence parameters and an initial success probability matching the baseline. Its conclusions are a strong law, central limit theorem, almost-sure non-Gaussian limit and iterated-logarithm laws. It contains no finite or limiting mode-count theorem. This settles that source comparison, but not the 1993 paper it cites.
- Drezner, *On the limit of the generalized binomial distribution* (2006), [publisher record](https://doi.org/10.1080/03610920500439950). The abstract gives Gaussian results in one parameter range and empirical non-Gaussian limits in another. **Read: abstract and bibliographic record only.**
- Drezner and Zerom, *Generalized binomial models for analytics and decision-making: capturing feedback dependencies* (2026), [publisher page](https://doi.org/10.1007/s10479-026-07255-1). **Read: abstract and the openly rendered appendices A–E; main text is subscription content and was not read.** The accessible material describes simulations, estimation and bimodality, without an accessible universal mode-count theorem.
- Murahara and Tokumitsu, *Optimal Rates in Local and Central Limit Theorems for the Elephant Random Walk*, [arXiv:2610.35019](https://arxiv.org/abs/2610.35019). **Read: abstract only.** This fresh October 2026 preprint concerns optimal diffusive and critical approximation rates, not a stated mode-count result.

### Inferences

The correlated Bernoulli recurrence `Pr(X_(n+1)=1|S_n)=(1-theta)*p+theta*S_n/n` contains positively correlated ERW counts at `p=1/2, theta=1-2 epsilon` with `epsilon≤1/2`. The first-step bias is an additional parameter in the present theorem. Original versions of the generalized binomial model often set the initial success probability equal to `p`; the separate initial-bias formulation must be checked in the original full texts. The present proof treats arbitrary initial bias directly, permits negative memory correlation as well, and gives an explicit oriented sign bound. GLRS's 2025 bias conjecture is evidence that the limiting classification remained unresolved, but it does not certify priority of every finite lemma.

### Gaps

The highest-priority missing full text is Drezner–Farnum (1993), followed by Drezner (2006) and the main text of Drezner–Zerom (2026). No email or library request was sent. Keep these as unresolved checks in any final novelty assessment.

## What did the independent manuscript review find?

The integrated biased theorem in `sec_bulk_applications.tex` and its proof in `app_modes.tex` were checked against the actual finite recurrence and the Lean declarations. The boundary ratio, sign orientation, endpoint biases, augmented-row propagation, zero extension and local-limit factor agree. No mathematical gap was found. The review requested explicit q-dependence when reusing `P_N`, cleaner reflected-difference superscripts, and an explicit formula for the physical density L1 approximation. These are presentation changes, not added assumptions.

The profile proof was checked independently through its interval-mass squeeze, moving concavity interval, secant peak bound, compact grid argument and tail unfolding. Its claim of uniform convergence uses the fair curvature partition; unimodality alone is not substituted for peak control. The truncated folded density is not claimed convex beyond its support endpoint.

`PaperD.BiasedModesList` subsequently compiled. Its `diff_signPattern` proves the manuscript's literal sign-subsequence statement for every increasing list of integer indices, including both zero-extension boundary differences. Focused axiom checks of `diff_signPattern` and `signPattern_of_no_pattern` returned only `propext`, `Classical.choice` and `Quot.sound`.
