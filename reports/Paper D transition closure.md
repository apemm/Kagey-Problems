# Paper D closes the shape questions

The revision establishes a unique fair-start modal transition and a centred interval of bimodal initial biases at every superdiffusive memory. The second result proves the conjecture in Guérin, Laulin, Raschel and Simon's Remark 2.1(b), including its endpoint convention. It follows from a finite-chain property that the Landau approximation does not supply. The transition lies in the existing bracket of width below \(3.3\times10^{-15}\), and its critical density is unimodal. The paper also identifies the older correlated-Bernoulli model explicitly and credits its limit theory. The numerical derivative certificate, all eight new Lean modules, the actual-model assembly and the complete project build have passed. The full axiom audit and manuscript package checks have also passed. The distinctions between written proofs, numerical enclosures and kernel-checked deductions are recorded below.

## One critical memory separates the two fair shapes

Write \(Q(a)=g_a''(0)\), where \(g_a\) is the fair-start superdiffusive density. The added certificate proves

\[
0.68<Q'(a)<0.70,
\qquad
-0.09<g_a^{(4)}(0)<-0.07
\]

throughout the interior of
\(I=[0.66881285,0.66881287]\). This interval strictly contains the existing rational bracket

\[
z_- = \frac{1838418790980431}{2748779069440000},
\qquad
z_+ = \frac{45960469774511}{68719476736000}.
\]

The fresh computation passed all 19 acceptance checks at 1600-bit precision with 1100 moments, under `python -O`. Its tighter displayed enclosures are \([0.6890\mathbin{\pm}8.16\times10^{-5}]\) for the parameter derivative and \([-0.07921\mathbin{\pm}4.05\times10^{-6}]\) for the fourth spatial derivative. The paper uses the conservative rational bounds, rather than those display-rounded values. ([Production certificate](../kagey-problems/problem131/paperD/certify_transition.py), [recorded output](../kagey-problems/problem131/paperD/data/transition_derivative_certificate.json))

The proof differentiates the conditional characteristic function's smoothing equation in the memory parameter. It includes both the derivative of its mixing weight and the derivatives of its scaled arguments. An inhomogeneous bootstrap then gives the uniform estimate
\(|\partial_a\phi_a(t)|\le4t^{-7}\) for \(t\ge6\). This integrable envelope justifies differentiation of the Fourier integral for \(Q\). Its contribution beyond frequency 10 is at most \(1/(10000\pi)\). Finite-frequency Taylor bounds cover the remaining integral and its discarded terms. In particular, the proof does not differentiate a previously bounded approximation error. ([Analytic derivation](../research_notes/Paper%20D%20transition%20closure/transition.md), [complete written proof](../kagey-problems/problem131/paperD/or_transition_proofs.tex))

The old endpoint signs and continuity give a zero \(a_*\in(z_-,z_+)\). The positive derivative makes it the only zero in that bracket. At \(a_*\), evenness and the negative fourth derivative give

\[
g_{a_*}'(x)
=\frac{g_{a_*}^{(4)}(0)}6x^3+o(x^3)<0
\quad\text{for sufficiently small }x>0.
\]

The central-increasing alternative of the existing fair-shape dichotomy is therefore impossible at criticality. Combining this with the old classification outside the bracket proves that the density is strictly unimodal for \(1/2<a\le a_*\) and strictly bimodal for \(a_*<a<1\). The transition's uniqueness is global in memory. ([Classification proof](../kagey-problems/problem131/lean/PaperD/Modes/TransitionClassification.lean), [existing threshold certificate](../kagey-problems/problem131/paperD/certify_threshold.py))

There is a necessary distinction between this conclusion and a global statement about curvature. The combined sign certificates show that \(Q\) has exactly one zero on \((1/2,839/1250]\), whose upper endpoint is 0.6712. They do not exclude additional isolated zeros of \(Q\) in the already bimodal region above it. Such zeros would not create another modal transition, and the theorem does not need to exclude them. The revision also does not add a square-root mode-separation theorem. ([Independent review](../research_notes/Paper%20D%20transition%20closure/bias_independent_review.md))

## Every memory has one centred open bias interval

For each \(a\in(1/2,1)\), there is \(b_a\in[0,1/2]\) such that the limit density has exactly two local maxima precisely when

\[
b_a<q<1-b_a.
\]

For every other \(q\in[0,1]\), including the two interval endpoints, it is unimodal with exactly one local maximum. The convention \(b_a=1/2\) represents an empty interval. Combined with the fair transition theorem, this gives \(b_a=1/2\) for \(a\le a_*\) and \(b_a<1/2\) for \(a>a_*\). The existing near-one profile theorem implies \(b_a\to0\) as \(a\uparrow1\). No assertion is made that \(b_a\) is strictly positive at each fixed memory, continuous or monotone in memory, or converges at a specified rate. ([Written proof](../research_notes/Paper%20D%20transition%20closure/bias_interval_proof.tex), [actual-model assembly](../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalAssembly.lean))

The missing structural fact is unimodality on the half-line favoured by the initial bias. For \(q\ge1/2\), the actual finite recurrence first proves reflection dominance,
\(P_{n,q}(k)\ge P_{n,q}(n-k)\) on the upper half. It then excludes a negative first difference followed by a positive one on that half. The proof includes the temporal outer boundary and the changing central index. At the parity step where one parent lies outside the preceding half, reflection dominance makes the new central difference nonnegative. The span-two lattice local limit transfers both properties to the density. ([Finite-chain proof](../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalFinite.lean), [local-limit transfer](../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalTransfer.lean))

The remaining argument concerns the reflected mixture
\(f_q(x)=q h(x)+(1-q)h(-x)\). On \(q\ge1/2\), reflection dominance and absence of a right-half valley make a strict valley equivalent to a strict descent at some \(x<y\le0\). Conditional unimodality implies \(h(x)\le h(y)\) there. Consequently,

\[
D(q)=f_q(x)-f_q(y)
\]

is affine in \(q\), with \(D(1)\le0\). If it is positive at one bias, it stays positive as that bias decreases towards one half. The valley biases are therefore downward closed on \([1/2,1]\). Strict inequalities make the set open, and reflection supplies its symmetric half. This proves connectedness for every memory without estimating small peaks near \(q=0\) or \(q=1\). ([Mixture argument](../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureInterval.lean))

A valley corresponds to two genuine local maxima, not merely two stationary points. Integrability supplies a lower point on each outer tail, and compact maximization gives a maximum on each side of the valley. Conversely, two local maxima have a lower point between them because analytic densities have no constant interval. The earlier all-bias theorem excludes a third maximum. With no valley, the same compactness argument gives one global maximum and monotonicity on either side. This assigns the boundary biases to the unimodal case and handles stationary shoulders. ([Mode equivalence](../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureIntervalModes.lean), [independent review](../research_notes/Paper%20D%20transition%20closure/bias_independent_review.md))

An exact rational check found no violation of the finite half-line properties in 2,560 rows, covering both parities, endpoint biases and negative as well as positive memory correlation. It helped check the boundary reasoning. It is not a certificate for limiting bias endpoints, and a grid of approximate endpoints is unnecessary for the connectedness claim once the proof is available. ([Probe and parameter grid](../research_notes/Paper%20D%20transition%20closure/bias_half_probe.py), [output](../research_notes/Paper%20D%20transition%20closure/bias_half_probe_output.json))

## The historical claim is now narrower and better sourced

The counting rule is the correlated-Bernoulli transition with \(p=1/2\) and \(\theta=1-2\varepsilon\). Its usual nonnegative-dependence parameter range covers \(0<\varepsilon\le1/2\), including all superdiffusive memories. An arbitrary initial bias changes the initial distribution, not the value of \(p\) in that transition. The revised introduction credits Drezner–Farnum for the model, Heyde for its constant-parameter limit regimes, and James–James–Qi for the time-varying extension. The paper's shape results and rare-reversal estimates are distinct from that older limit theory. ([Revised introduction](../kagey-problems/problem131/paperD/sec_intro.tex), [source comparison](../research_notes/Paper%20D%20transition%20closure/literature.md))

The source record must distinguish an article read in full from an attribution checked in a later paper.

| Source | What was read in this pass | What it supports or leaves open |
| --- | --- | --- |
| [James, James and Qi (2008)](https://doi.org/10.1016/j.spl.2008.01.104) | All seven pages of the [author copy](https://www.d.umn.edu/~yqi/mydownload/08letter.pdf), including proofs and references | Exact transition rule, time-varying limit theorem and explicit attribution of the constant-parameter regimes to Heyde. No mode-count theorem is stated. |
| [Heyde (2004)](https://doi.org/10.1111/j.1467-842X.2004.00311.x) | Publisher abstract and ANU bibliographic record. Its result was also checked as stated in James–James–Qi's introduction. | The five-page original was not obtained or read in full. That comparison remains incomplete. |
| [Drezner and Farnum (1993)](https://doi.org/10.1080/03610929308831202) | Previously checked publisher record and abstract | Full text is pending the user's library request. Priority for the finite-modality theorem remains qualified. |
| [Guérin, Laulin, Raschel and Simon, arXiv v1](https://arxiv.org/html/2409.06836v1#S2) | Introduction, Section 2 conditional-unimodality proof, Remark 2.1 and relevant adjacent statements | Direct comparison with the shape questions and exact endpoint convention. Targeted rereading; the whole paper and publisher PDF were not reread. |
| [Trinas and Valle, arXiv v1](https://arxiv.org/html/2609.14753v1) | Abstract, all mathematical Sections 1–5, statements, proofs, discussion and references | Mathematical text read in full through HTML. Their code and certificates were not inspected or rerun. The all-bias local limit is an input; their endpoint-bias log-concavity work addresses a different conjecture. |
| [Peres and Qin, arXiv v2](https://arxiv.org/html/2604.07227v2) | Current abstract, version record, introduction and model definition | Partial relevance screening of transition-probability bounds on groups and graphs. |
| [Gut and Stadtmüller, JTP 2026](https://link.springer.com/article/10.1007/s10959-026-01517-1) | Abstract and relevant opening paragraphs | Partial relevance screening of a Bernoulli variant motivated by stops and restricted memory. |
| [Fang, JSP 2026](https://link.springer.com/article/10.1007/s10955-026-03646-7) | Abstract and opening motivation and model | Partial relevance screening of initial training and return-time scales. |

The fresh comparison confirms that GLRS Remark 2.1(b) specifies an open bimodal interval, with its endpoints unimodal and a radius allowed to lie in \([0,1/2]\). Setting that radius equal to \(1/2-b_a\) recovers its statement exactly. It is therefore accurate to say that the new interval theorem proves this conjecture; strict positivity of \(b_a\) is not required by its wording. That mathematical implication is distinct from a claim to be the first proof. A targeted literature search through 1 November 2026 found no later resolution of this conjecture or the unique fair-start modal transition, but it was not an exhaustive priority search. The pending Drezner–Farnum full text still limits the finite-theorem priority comparison. ([Fresh novelty and reading audit](../research_notes/Paper%20D%20transition%20closure/novelty.md), [GLRS Remark 2.1(b)](https://arxiv.org/html/2409.06836v1#S2))

Trinas and Valle's later shape analysis concerns log-concavity at the endpoint bias \(q=1\), corresponding to GLRS Remark 2.3. Its thresholds should not be compared with the fair-start modal threshold as if they measured the same change. The other screened papers have different principal questions, but partial reading does not exclude every possible overlapping result. ([Trinas–Valle mathematical text](https://arxiv.org/html/2609.14753v1), [scope of the later-paper checks](../research_notes/Paper%20D%20transition%20closure/novelty.md))

## Formal checks have explicit boundaries

The new finite recurrence arguments, local-limit transfer, reflected-mixture classification and mode equivalence are Lean proofs. All eight new modules compile, including the actual-model assembly and the endpoint-limit proof. The assembly derives reflection dominance, the half-line property, absence of flat intervals and the mode bound from the established recurrence, Fourier inputs and lattice local limits. It does not assume the new interval conclusion. The complete project build has also passed. The complete audit covers 361 modules and 23,841 theorem and lemma declarations, with no unimported files. Every declaration uses only `propext`, `Classical.choice`, `Quot.sound`, or a subset. All source hashes still match. The 28 build warnings concern linters or deprecations, not proof errors. ([Finite proof](../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalFinite.lean), [assembly](../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalAssembly.lean))

For the transition, `TransitionBounds.lean` proves the inhomogeneous bootstrap, dominated differentiation of the Fourier integral and the deduction of a positive derivative from a complete numerical enclosure. `TransitionClassification.lean` separates a locally unique curvature zero from the globally unique modal transition. The gamma, reciprocal-gamma and power-series enclosures are computed by Arb and checked by executable interval tests. They have not been reconstructed as proofs inside Lean. The detailed characteristic-function differentiation and half-interval integral reduction remain written analytic arguments, with their resulting hypotheses explicit in the formal interface. The existing published local-limit and Fourier results, and the earlier weak bridge's documented formalization boundary, remain unchanged. ([Formal transition interface](../kagey-problems/problem131/lean/PaperD/Modes/TransitionBounds.lean), [classification](../kagey-problems/problem131/lean/PaperD/Modes/TransitionClassification.lean), [written numerical reduction](../kagey-problems/problem131/paperD/or_transition_proofs.tex))

The literature pass removed 396 words from the introduction even after adding the historical paragraph. That pass preserved every introduction theorem environment and displayed formula, the epigraph and its callback, and the exact AI statement. Its recorded disclosure hash remains `ed20652c6d4be4b2b4eab60960d73bbd0a1b1487f596bd7a8de6fb506288593d`. Later theorem strengthening intentionally changes some introduction statements, so the earlier equality check is evidence for that editing pass, not a final whole-revision audit. The final comparison confirms the same disclosure hash, together with preservation of the epigraph, callback and acknowledgments. ([Prose-edit check](../research_notes/Paper%20D%20transition%20closure/literature-edit-checks.json))


## Final manuscript and release checks

The journal PDF is 51 pages, unchanged from the preceding revision despite the two stronger conclusions. The extended PDF is 72 pages and the complete threshold review extract is 9 pages. The crossing and shape sections lost 607 redundant words across two checked passes. All 72 protected mathematical blocks and every distinct inline formula in those sections remain unchanged. The introduction and verification section were shortened separately; strengthened theorem statements were intentionally updated. ([Prose checks](../research_notes/Paper%20D%20transition%20closure/trim.md))

Both source archives rebuild in isolation. The PDF text matches those independent builds, all cited bibliography entries resolve, every font is embedded, and the TeX logs have no overfull boxes or undefined references. Nine representative pages were rendered and inspected. The 14 reviewed original threshold files still match commit `b3fe997` byte for byte. The disclosure, epigraph, callback and acknowledgments are unchanged. ([Verification record](paperD-transition-2026-11-01/README.md), [final source checks](paperD-transition-2026-11-01/final-state.json), [PDF checks](paperD-transition-2026-11-01/pdf-checks.json))

The manuscript, README and arXiv metadata identify `paperD-arxiv-v2`. The release runners record the exact source commit, a fresh seven-script numerical check and a final Lean rebuild against the audited source hashes. The numerical check includes a full fresh run of the new derivative certificate. For the older threshold certificate it checks archived runs and three fresh probes, rather than repeating all nine heavy jobs. The existing `paperD-arxiv-v1` is retained. No journal submission, arXiv upload or email is part of this revision.
