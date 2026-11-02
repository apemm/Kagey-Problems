# Bias limits strengthen elephant mode theory

Paper D now proves an at-most-two-mode theorem for **every initial bias**, both at finite time and for the superdiffusive limit. The finite proof covers every nondegenerate memory probability and is checked in Lean from the existing conditional count law, without a shape assumption or an external probabilistic theorem. The limit proof uses explicit Fourier and local-limit literature inputs. A second checked argument upgrades the existing near-one weak bridge to uniform Landau density profiles, total variation approximation, mode locations and peak heights. For biases bounded away from zero and one, it proves that exactly two modes occur at sufficiently high memory, with locations and weighted heights controlled uniformly in the bias. The full-library build and axiom audit passed across 353 modules and 23,777 declarations. The numerical transition work remains a research prototype, and historical comparisons with the generalized-binomial literature remain open.

## First differences control every initial bias

Let the flip probability be \(0<\varepsilon<1\), put \(a=1-2\varepsilon\), and let \(q\in[0,1]\) be the probability of a positive first step. Write \(P_n(k)\) for the probability of \(k\) positive steps after \(n\) steps, extended by zero to all integers. The new theorem states that the first differences
\[
d_n(k)=P_n(k+1)-P_n(k)
\]
have no four ordered positions with strict signs \(-,+,-,+\). Equivalently, after removing zeros and merging equal adjacent signs, the pattern is a subsequence of \((+,-,+,-)\). **Three distinct modal plateaus are impossible.** The result covers every \(n\ge1\), not only a crossing time or a limiting distribution. The precise declarations are `diff_no_pattern` and `no_four_increments` in [BiasedModes.lean](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/lean/PaperD/BiasedModes.lean>). The literal sign-pattern formulation, `diff_signPattern`, also compiles in [BiasedModesList.lean](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/lean/PaperD/BiasedModesList.lean>).

The proof uses the actual biased law
\[
P_n(k)=q f_n(n-k)+(1-q)f_n(k),
\]
where \(f_n\) is the already formalized conditional count law. Its interior first differences satisfy
\[
d_{n+1}(k)=r_n(k-1)d_n(k-1)+[1-r_n(k+1)]d_n(k),
\qquad r_n(k)=\varepsilon+ak/n,
\]
for \(1\le k\le n-1\). Both coefficients are positive in that range. The boundary terms require a separate argument; extending the positivity assertion beyond the interior would be a mistake.

For \(q<1\), the left endpoint ratio \(\xi_n=P_n(1)/P_n(0)\) satisfies
\[
\xi_{n+1}=(1-b/n)\xi_n+A,
\quad b=\frac{1-2\varepsilon}{1-\varepsilon}<1,
\quad A=\frac{\varepsilon}{1-\varepsilon}>0.
\]
Its increments obey
\[
\delta_{n+1}=\frac{n-b}{n+1}\delta_n+\frac{A}{n+1}.
\]
Once an increment becomes nonnegative, every later increment is positive. This makes the ratio decrease and then increase, with either part allowed to be empty. When \(q\le1/2\), the left boundary differences therefore have temporal pattern \((-,+)\), while reflection gives \((-,+,-)\) on the right. Appending future boundary values to each interior row creates an initial \((+,-,+,-)\) pattern, which the positive interleaving recurrence preserves. Reflection handles \(q\ge1/2\); the endpoint bias \(q=0\) is handled directly by the support of the conditional law, and \(q=1\) follows by reflection. This is the essential mechanism, and it is short enough to present in the paper rather than hide behind a large computational certificate.

The original curvature extension is false. At \(a=24/25\), \(q=1/1200\), and \(n=80\), second differences have signs \(-,+,-,+,-\) at positions \(1,2,74,75,77\). A separate exact calculation at \(a=9/10\), \(q=199/200\) gives five alternating signs in the temporal edge curvature. Both were verified using rational arithmetic. These counterexamples explain why the first-difference proof adds something beyond repeating the fair-start curvature argument. The reproducible [probe](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Paper D transition and modes/probe_bias.py>) and [output](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Paper D transition and modes/probe_bias_results.json>) also check 182,364 bias sign cells over a finite grid through \(n=4000\). They found no third mode, but the kernel-checked theorem, rather than the floating-point sweep, supports the claim.

For the superdiffusive limit, the required normalization is exact. Trinas–Valle prove
\[
\sup_{j\equiv n\;(2)}
\left|\frac{n^a}{2}\Pr(S_n=j)-f_{q,a}(j/n^a)\right|\to0,
\qquad \frac12<a<1.
\]
Set \(k_n(x)=\lfloor(n+n^a x)/2\rfloor\). Then \(j_n(x)=2k_n(x)-n\) has the correct parity and \(0\le x-j_n(x)/n^a<2n^{-a}\). Thus \((n^a/2)P_n(k_n(x))\to f_{q,a}(x)\), with no extra Gamma normalization. Three local maxima of a continuous density without a constant interval produce five ordered values with four strict alternating increments. The local limit transfers those inequalities back to the finite rows, contradicting the new theorem. The compiled `biased_limit_modes_of_smoothing` assembles this argument with the Fourier proof of analyticity and absence of constant intervals. The local-limit theorem remains an explicit literature input. ([Trinas–Valle, Theorem 3.1](https://arxiv.org/html/2609.14753v1))

## Curvature upgrades weak convergence to peak profiles

Write \(h_a\) for the positive-first-step density and \(g_a(x)=\{h_a(x)+h_a(-x)\}/2\) for the fair density. With
\[
A_\varepsilon=1+2\varepsilon\log(1/\varepsilon),
\qquad s_\varepsilon=2\varepsilon,
\]
the conditional and folded profiles are
\[
K_\varepsilon(z)=s_\varepsilon h_{1-2\varepsilon}
 (A_\varepsilon-s_\varepsilon z),\qquad
H_\varepsilon(z)=2s_\varepsilon g_{1-2\varepsilon}
 (A_\varepsilon-s_\varepsilon z)
 \mathbf1_{\{z<A_\varepsilon/s_\varepsilon\}}.
\]
The existing martingale bridge supplies weak convergence of the conditional profile to the Landau density \(f_L\). The new argument derives, rather than assumes, off-mode density convergence from interval masses and unimodality. It then uses the fair density's convex–concave–convex shape to control the modal value. **Unimodality by itself is insufficient for uniform convergence at the peak**, because it permits a thin spike there.

The peak argument is concrete. Strict midpoint inequalities for three fixed points on either side of the Landau mode force the approximating concavity interval to contain a fixed neighborhood of that mode. A secant slope inside this interval bounds the moving maximum from above. Its lower bound comes from the value at a nearby fixed point. Monotonicity and a finite grid then give uniform convergence on bounded intervals, and monotone tails control the rest of the line. The folded profile is truncated at a moving endpoint; its right convexity is used only below that endpoint. Extending convexity through the truncation would be incorrect. The derivation and source comparisons are recorded in [near_one.md](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Paper D transition and modes/near_one.md>).

The resulting deterministic theorem takes density normalization, conditional unimodality, the fair curvature partition, interval-mass convergence and standard Landau shape properties as inputs. Its conclusions include both uniform profiles, conditional \(L^1\) convergence, and
\[
c_{1-2\varepsilon}
=1+2\varepsilon\log(1/\varepsilon)-2\varepsilon\lambda_L+o(\varepsilon),
\qquad
4\varepsilon g_{1-2\varepsilon}(c_{1-2\varepsilon})\to f_L(\lambda_L).
\]
Here \(\lambda_L\) is the unique Landau mode and \(c_a\) is the positive fair mode. The final entry is `near_one_profiles_of_probability_bridge` in [RevisionNearOne.lean](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/lean/PaperD/Modes/RevisionNearOne.lean>), which has compiled. It starts from weak convergence of probability measures with the actual scaled conditional densities. Portmanteau supplies the interval masses used by [NearOneFromMass.lean](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/lean/PaperD/Modes/NearOneFromMass.lean>). The final entry derives the fair curvature partition from the existing walk-law, conditional Fourier and fourth-moment inputs. It also derives the strict Landau maximum and local concavity from the existing mode certificate. It does not assume the new profile or peak conclusions. The old martingale proof of the weak bridge remains outside this formalization and is an explicit input.

The conditional profile also gives a two-component approximation valid uniformly in spatial location and in \(q\in[0,1]\):
\[
\sup_{q,x}\left|
s_\varepsilon f_{q,1-2\varepsilon}(x)
-qf_L\!\left(\frac{A_\varepsilon-x}{s_\varepsilon}\right)
-(1-q)f_L\!\left(\frac{A_\varepsilon+x}{s_\varepsilon}\right)
\right|\to0.
\]
The proof is a weighted triangle inequality after the conditional uniform limit. The corresponding density \(L^1\) approximation, including its physical rescaling, is also checked and holds uniformly over \(q\in[0,1]\). For each fixed \(0<\eta\le1/2\), two disjoint Landau windows contain local maxima uniformly over \(q\in[\eta,1-\eta]\) at sufficiently high memory. Combining this with the at-most-two theorem gives exactly two modes, with positive and negative locations \(A_\varepsilon-s_\varepsilon\lambda_L+o(s_\varepsilon)\) and \(-A_\varepsilon+s_\varepsilon\lambda_L+o(s_\varepsilon)\). Their scaled heights converge to \(qf_L(\lambda_L)\) and \((1-q)f_L(\lambda_L)\), uniformly over that bias interval. The final declaration `NearOneProfileConclusions.biased_modes` has compiled. It derives its mode-count and no-flatness conditions from the biased lattice local limits and conditional Fourier inputs; neither condition is assumed in the exported result. No analogous uniform two-mode claim is made for biases approaching an endpoint arbitrarily fast.

These limits concern memory approaching one. They do not follow merely from fixed-memory tail asymptotics or from the time-asymptotic local limit theorem. The limiting stable density's shape is supported by the bell-shape literature, but the precise historical comparison of the general weak-to-density principle remains incomplete. Paper D should claim the ERW scaling result and its peak geometry, not a new general convergence principle. ([Guérin–Laulin–Raschel–Simon](https://doi.org/10.1214/25-EJP1362); [Kwaśnicki](https://doi.org/10.1090/tran/7825))

The profile also explains why variance gives a misleading width for the concentrated part of the law. In the present parametrization, the known variance expansion is \(\operatorname{Var}(\mathcal L_{1-2\varepsilon})\sim4\varepsilon\). Its standard deviation is therefore of order \(\sqrt\varepsilon\), whereas the Landau profile varies on scale \(\varepsilon\). The modal displacement from one is larger still than that profile width by a logarithmic factor. This is a mathematical consequence of the different asymptotic scales, not a claim of moment convergence to the Landau law. ([Trinas–Valle, equation 4.5](https://arxiv.org/html/2609.14753v1))

## Transition uniqueness remains a separate proof obligation

The transition calculations are stronger than a numerical plot but weaker than a finished theorem under the requested verification standard. The differentiated-smoothing prototype reports
\[
0.6889315<\partial_a g_a''(0)<0.6890685
\quad\text{for }0.66881285\le a\le0.66881287,
\]
and a separate prototype reports
\[
-0.081<g_a^{(4)}(0)<-0.079
\quad\text{for }0.6688\le a\le0.6692.
\]
These are the stored Arb outputs of [probe_parameter_tail.py](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Paper D transition and modes/probe_parameter_tail.py>) and [probe_transition.py](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Paper D transition and modes/probe_transition.py>). Their full derivation is in [transition.md](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/research_notes/Paper D transition and modes/transition.md>).

The new technical idea is to differentiate the smoothing equation and prove an inhomogeneous Fourier-tail bound for the parameter derivative. It does not differentiate a previously obtained uniform error bound, which would be invalid. The prototype accounts for the derivative of the mixture weight, the derivatives of the scaled Fourier arguments and the omitted parameter Taylor series. Its recorded parameter-tail error is below \(1.872\times10^{-5}\). The open work is independent checking of that derivation, export of checkable transcendental enclosures, and formal linkage from those enclosures to the actual characteristic function. The released threshold certificate has not been replaced by this prototype.

If those obligations close, let \(Q(a)=g_a''(0)\), let \(a_*\) be its zero, and put \(R_*=g_{a_*}^{(4)}(0)<0\). Positive \(Q'(a)\) on an interval containing every possible zero would prove uniqueness. Taylor's theorem and the shape classification would then give
\[
c(a)\sim\sqrt{-6Q'(a_*)/R_*}\sqrt{a-a_*},
\qquad
g_a(c(a))-g_a(0)\sim
-\frac{3Q'(a_*)^2}{2R_*}(a-a_*)^2.
\]
Without a proved parameter derivative, the corresponding square-root law can only be formulated in the curvature variable \(Q(a)\), not in memory. A generic Taylor lemma has compiled, but it does not supply the ERW derivative signs. **Neither a unique transition nor a memory pitchfork is currently claimed as a verified new manuscript theorem.**

The same distinction applies to the broader bias conjecture. The finite theorem rules out three modes, and the near-one profile proves and localizes two modes for each fixed interior bias. Neither assertion proves that, for every memory parameter, the set of bimodal biases is a single interval centered at one half. A numerical grid found no disconnected bias intervals; that observation does not settle the conjecture.

## Novelty depends on a few specific full texts

Guérin–Laulin–Raschel–Simon prove conditional unimodality and explicitly conjecture a centered unimodal/bimodal classification in the initial bias. The present all-bias mode bound and near-one profile target that open shape problem. The underlying correlated-Bernoulli model is older, however. Drezner–Farnum's 1993 generalized-binomial article discusses both unimodal and bimodal distributions, and its full text has not yet been obtained. The accessible abstract is insufficient to decide whether a universal finite mode bound is already present. The proper novelty statement is therefore bounded: the checked ERW sources do not give these conclusions, while **finite-theorem priority remains subject to the generalized-binomial comparison**. ([GLRS](https://arxiv.org/html/2409.06836v1); [Drezner–Farnum](https://doi.org/10.1080/03610929308831202))

The reading record below distinguishes complete reading from targeted inspection. An accessible article page is not counted as reading the full paper, and reading a certificate's description is not counted as rerunning it.

| Source | What was actually read in this investigation | Comparison still needed |
|---|---|---|
| [Trinas–Valle, 2026](https://arxiv.org/html/2609.14753v1) | Full mathematical text, Sections 1–5 and references | Its certificates were not rerun; its fixed-memory theorem supplies the shape-transfer input |
| [Guérin–Laulin–Raschel–Simon, 2025](https://arxiv.org/html/2409.06836v1) | Introduction, complete Section 2 unimodality argument, bias conjecture, relevant moment-growth statements | No whole-paper reread claimed; fixed-memory tails do not establish the near-one profile |
| [Guérin–Laulin–Raschel](https://arxiv.org/pdf/2308.14630) | Opening results and density proof's Fourier-bootstrap step | No whole-paper reread claimed |
| [González Rangel, 2026](https://arxiv.org/html/2607.15125v1) | Introduction, principal theorem and Section 2 asymptotic extraction | Does not supply the required complex-memory tail estimate; not read in full |
| [Kwaśnicki, 2020](https://doi.org/10.1090/tran/7825) | Introduction through Corollary 1.3 | Full proof not read; inflection-point migration remains a proposed extension |
| [Hettmansperger–Klimko, 1974](https://doi.org/10.1214/aos/1176342722) | Bibliographic record and abstract-level claim | **Full text needed** for the exact historical weak-to-density comparison |
| [Boos, 1985](https://repository.lib.ncsu.edu/server/api/core/bitstreams/4c94a3a3-6c4c-4e4b-9e7b-9b7c52e845bf/content) | Indexed first-page excerpt checked; the repository link presents a bot-detection page to the reader tool | **Full text still unread**; the excerpt confirms an equicontinuity argument but does not replace reading the theorem and proof |
| [Drezner–Farnum, 1993](https://doi.org/10.1080/03610929308831202) | Abstract and publisher record; PDF returned 403 | **Highest-priority full text needed** for finite shape claims |
| [James–James–Qi, 2008](https://www.d.umn.edu/~yqi/mydownload/08letter.pdf) | All seven pages, including the full proofs and references | Comparison resolved: verifies the older recurrence and its asymptotic limit theory, but states no mode-count theorem |
| [Drezner, 2006](https://doi.org/10.1080/03610920500439950) | Abstract and publisher record | **Full text needed** for the older limiting-shape discussion |
| [Drezner–Zerom, 2026](https://doi.org/10.1007/s10479-026-07255-1) | Abstract and openly rendered appendices A–E | **Main text needed**; accessible material describes simulation and estimation |
| [Murahara–Tokumitsu, 2026](https://arxiv.org/abs/2610.35019) | Abstract only | Concerns diffusive and critical approximation rates; no mode-count result stated in the abstract |

No library request or email was sent. The missing texts should be obtained before replacing the bounded comparison above with a first-priority claim. The general parameter-dependent smoothing-transform literature also needs a focused comparison if the transition-sensitivity method becomes a headline result.

## Verification should determine the manuscript claims

The final source-level entries have compiled, and the all-bias entire-extension theorem passed its direct Lean check. Focused axiom audits of the finite theorem, recurrences and literal sign-pattern theorem reported only `propext`, `Classical.choice` and `Quot.sound`. The finite proof contains no `sorry`, added axiom, numerical oracle or assumed mode-count conclusion. An independent review checked the integrated boundary proof, local-limit normalization and profile argument against the formal statements.

| Manuscript result | Final Lean declaration | Explicit inputs beyond the finite recurrence |
|---|---|---|
| Proposition F.5: finite two-mode bound | `BiasedModes.diff_signPattern`; `BiasedModes.no_four_increments` | None; the count law is the existing formalized finite law |
| Theorem 4.6: biased limit has at most two local maxima | `Modes.biased_limit_modes_of_smoothing` | Conditional Fourier smoothing inequality, Fourier density representation, density integrability and nonzero mass, and the span-two lattice local limit |
| Lemma F.4: entire extension for every bias | `Modes.biased_entire_extension_of_smoothing` | Conditional Fourier continuity, unit bound, modulus symmetry, tail decay, smoothing inequality and density representation |
| Theorem 4.7: uniform profiles, fair mode and height, uniform-bias total variation | `Modes.near_one_profiles_of_probability_bridge` | Existing `DensityHyp`, `LawConvHyp`, `ConditionalFourierHyp`, `GLRFourthMomentsHyp`; conditional normalization and GLRS unimodality; the old probability-measure weak bridge; Landau density and tail facts and `LandauModeHyp` |
| Corollary 4.8: exactly two biased modes with uniform positions and heights | `Modes.NearOneProfileConclusions.biased_modes` | The preceding profile conclusion plus actual biased Fourier representations and lattice local limits; the result derives absence of flat intervals and the mode-count bound |

The declaration names in this table have the common prefix `Kagey131.PaperD`. The full build and axiom audit passed across **353 modules and 23,777 declarations**, with zero unimported files and only `propext`, `Classical.choice` and `Quot.sound`. The build reports 24 linter or deprecation warnings. The [verification manifest](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/reports/paperD-strengthening-2026-11-01/verification-manifest.json>) records `all_checks_passed: true`; the [build log](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/reports/paperD-strengthening-2026-11-01/build-log.txt>) and [reproduction guide](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/reports/paperD-strengthening-2026-11-01/README.md>) preserve the evidence. The separate [final-state check](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/reports/paperD-strengthening-2026-11-01/final-state.json>) passed all 353 source hashes, the unchanged disclosure, tag references and byte-for-byte agreement of 14 reviewed certificate files with commit `b3fe997`.

The integrated journal manuscript has 51 pages and the extended version has 70. The revision adds the all-bias shape theorem and the high-memory profiles while preserving the existing disclosure unchanged. The old weak-bridge proof and previously documented certificate limitations remain explicit. Unique-transition, memory-pitchfork and centered-bias-interval claims stay outside the theorem list until their separate proof obligations close. The resulting scope is stronger without treating either incomplete source comparisons or exploratory interval calculations as settled mathematics.
