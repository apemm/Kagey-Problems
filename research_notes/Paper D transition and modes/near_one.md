# Near-one peak profiles, heights, and curvature

## What stronger result follows from the existing bridge and shape theorem?

### Takeaway

The result now proved in the generic formalization is a uniform Landau profile for both the folded fair-start density and the positive-first-step density. It yields an explicit fair-mode displacement and peak height, and a two-component approximation uniform over every initial bias. The curvature partition is essential at the peak; unimodality alone does not prevent a thin density spike there.

### Cited Findings

- The manuscript already proves weak convergence of `(1-L_(1-2ε))/(2ε)+log(1/ε)` to the Landau law. Its martingale bridge is in [sec_bulk_applications.tex](../../kagey-problems/problem131/paperD/sec_bulk_applications.tex).
- Guérin, Laulin, Raschel and Simon prove unimodality for the fixed positive first step, and explicitly leave the shape of biased reflected mixtures open. The inspected proof establishes the finite-time unimodality before taking a weak limit. See Theorem 1.1, Section 2, and Remark 2.1(b), [published article DOI](https://doi.org/10.1214/25-EJP1362), [author manuscript](https://arxiv.org/html/2409.06836).
- The new Paper D strict-shape theorem gives one concavity interval around each positive peak, with convex intervals on either side. Its formal statement is in [RevisionShape.lean](../../kagey-problems/problem131/lean/PaperD/Modes/RevisionShape.lean).

### Inferences

Write

`Aε = 1 + 2ε log(1/ε)`, `xε(z)=Aε−2εz`, and

`Hε(z)=4ε g_(1−2ε)(xε(z)) 1{xε(z)>0}`.

This is the density of `(1−|L_(1−2ε)|)/(2ε)+log(1/ε)`. The existing weak bridge also gives this folded weak limit, because `P(L_(1−2ε)<0)→0`. Its mode is `mε=(Aε−c_(1−2ε))/(2ε)`.

The profile conclusions are:

1. `sup_z |Hε(z)−f_L(z)|→0`.
2. `mε→λ_L`, or equivalently `c_(1−2ε)=1+2ε log(1/ε)−2ελ_L+o(ε)`.
3. `4ε g_(1−2ε)(c_(1−2ε))→f_L(λ_L)`.
4. For the conditional density `h_a`, `Kε(z)=2ε h_(1−2ε)(Aε−2εz)` converges to `f_L` both uniformly and in L1.
5. For every initial bias `q∈[0,1]`, the density `q h_a(x)+(1−q)h_a(−x)` has the corresponding two reflected Landau profiles. The error bounds are uniform in `q`, including biases that vary with memory.

The argument separates into five elementary steps.

1. **Weak convergence and unimodality.** Equal-length interval averages locate the conditional mode. A continuous unique strict global maximum suffices: compare a short interval near that maximum with one on its proposed wrong side. Local averages then squeeze the conditional density at every point away from the limiting mode. Scheffé's argument gives conditional L1 convergence. The identity `Hε(z)=Kε(z)+Kε(2Bε−z)` below `Bε=Aε/(2ε)` gives the folded pointwise limit: a unimodal unit density with mode `b` satisfies `k(y)≤1/(y−b)` for `y>b`, so the reflected term vanishes uniformly on the receding tail.
2. **Exclude intruding convex tails.** Choose three fixed points on each side of `λ_L`, within its certified strictly concave neighborhood. Their strict midpoint inequality survives pointwise convergence. A convex tail cannot contain any of those triples. Hence the profile's concavity interval eventually contains a fixed neighborhood of `λ_L`.
3. **Control the peak.** For fixed `ℓ<x<λ_L` in that neighborhood and large enough indices, concavity bounds the moving peak by

   `Hε(mε) ≤ Hε(x)+(mε−x)(Hε(x)−Hε(ℓ))/(x−ℓ)`.

   First take `ε→0`, then `x↑λ_L`. The upper bound tends to `f_L(λ_L)`; the lower bound follows from `Hε(mε)≥Hε(x)`.
4. **Upgrade to uniform convergence.** Away from the peak, monotonicity and a finite grid squeeze the profile against the continuous limit. Near the peak, use the converging peak height and two nearby endpoint values. Monotonicity plus the vanishing tails of `f_L` controls both unbounded tails.
5. **Undo the scaling.** The mode remainder divided by `ε` is exactly `−2(mε−λ_L)`. The height identity follows from the density change of variables.

The same folding identity transfers the folded uniform limit back to the conditional density, using the receding-tail bound. Reflection and convex mixing contract both supremum and L1 errors. Thus no extra regularity of biased mixtures is needed for the uniform-in-bias approximation.

The folded profile is discontinuous at its right support endpoint, where it is set to zero. Thus its right convexity assertion must stop at that endpoint. That endpoint tends to positive infinity; every fixed witness interval eventually lies below it. Claiming global convexity after truncation would be incorrect.

### Gaps

- `NearOneFromMass.near_one_profiles_of_interval_masses` has compiled. Its input is conditional interval-mass convergence, original density normalization and unimodality, the fair-density curvature partition, and the stated Landau properties. It concludes both uniform profiles, the fair mode and height limits, and conditional L1 convergence. The interval-mass, pointwise and L1 steps are proved in `NearOneMass`, `NearOnePointwise`, and `NearOneL1`; the modal upgrade is proved in `NearOneMode`, `NearOneModeUnique`, `NearOnePeak`, `NearOneUniform`, `NearOneFoldShape`, and `NearOneProfile`.
- `NearOneMixture.uniform_biased_profile` has compiled. It proves the physical two-component supremum approximation uniformly in `q`. `NearOneMixtureL1` has also compiled: it proves the L1 contraction, the exact physical rescaling identity, and `uniform_physical_biased_profile_l1`.
- `NearOneNormalization` has compiled: original density normalization gives transformed density normalization, and the actual near-one fold boundary tends to infinity. `NearOneUnfold` and `NearOneMixture` prove the conditional-to-folded and folded-to-conditional implications, rather than assuming independent folded convergence.
- The old fixed-memory martingale bridge remains an explicit pre-existing input. The resulting theorem is not an unconditional formal derivation of that old bridge. Existing published probability/density inputs and the certified Landau inputs remain visible in the final interface.
- Exact biased-mode counting requires the separate no-three-local-maxima theorem and finite-window construction; it is not a consequence of uniform convergence alone.

### Final interface and its explicit inputs

The single entry module is `PaperD.Modes.RevisionNearOne`. Its theorem
`near_one_profiles_of_probability_bridge` returns
`NearOneProfileConclusions`. The entry module and its biased-mode corollary
have compiled successfully with Lean 4.33.1. The following table separates
genuine inputs from newly proved steps.

The complete Paper D audit passed after this assembly: 353 modules, 23,777
theorem/lemma declarations, and no unimported source files. Every checked
declaration uses only the allowed axioms `propext`, `Classical.choice`, and
`Quot.sound`. The [build log](../../kagey-problems/problem131/paperD/verification/build-log.txt)
and [verification manifest](../../kagey-problems/problem131/paperD/verification/verification-manifest.json)
record the exact source hashes and results. These checks do not erase the
explicit probability, literature, and numerical-certificate inputs listed next.

| Input or obligation | Status and source |
|---|---|
| Positive sequence `ε_n→0`, restricted to `ε_n≤1/10` | Deterministic near-one parametrization; restricting an arbitrary sequence to its tail imposes no limiting restriction. |
| `DensityHyp`, `LawConvHyp`, `ConditionalFourierHyp`, `GLRFourthMomentsHyp` for the fair law | Existing explicit walk-law, Fourier smoothing, and exact moment inputs. `strict_bimodal_four_fifths` derives the strict mode and curvature partition from them. The final wrapper does not assume the new peak shape. |
| Conditional density is nonnegative, integrable, and normalized; `g=(h+h∘neg)/2` | The physical definition of the conditional and fair laws. Affine normalization and the folded-density identity are proved in the new modules. |
| Conditional unimodality | Published GLRS input. The new proof allows any selected conditional mode; its scaled localization is a conclusion. |
| Weak convergence of probability measures with the actual scaled conditional densities | The old fixed-memory martingale bridge, explicit rather than silently assumed formalized. `NearOneWeak` derives interval-mass convergence by Portmanteau. |
| Continuous probability density `f_L`, vanishing at both infinities | Existing Landau density/Fourier facts. |
| `LandauModeHyp` | Existing certified mode/second-derivative input. The wrapper derives a unique strict maximum and strict concavity on radius `1/12500`; these are not additional asserted Landau properties. |
| Off-mode convergence, L1 convergence, fair modal location/height, global uniform convergence | New conclusions with kernel-checked component proofs. |
| Uniform-in-bias supremum and physical L1 bounds | New reflection/mixing contractions and affine identities, compiled in `NearOneMixture` and `NearOneMixtureL1`. |
| Exactly two biased modes, uniformly for `η≤q≤1−η` | The compiled `NearOneProfileConclusions.biased_modes` joins the profile conclusions to actual biased lattice local limits and Fourier representations. It derives `NoTwoValleys` from the finite-walk theorem and no flat intervals from Fourier smoothing, then uses the compact-window construction. Neither mode-count condition is an input to the exported corollary. |

The full proof fragment for manuscript integration is
[`near_one_profile_proof.tex`](near_one_profile_proof.tex). It makes the
mode-height argument explicit rather than treating weak convergence as
automatically uniform convergence.

## Which prior results overlap, and what was actually read?

### Takeaway

The general unimodal weak-to-strong principle is classical. The proposed new contribution is its ERW scaling limit together with the curvature-based removal of the modal exception, the explicit peak displacement, and the peak-height asymptotic.

### Cited Findings

- Hettmansperger and Klimko, *A note on the strong convergence of distributions*, Annals of Statistics 2 (1974), 597–598, [DOI](https://doi.org/10.1214/aos/1176342722), [JSTOR](https://www.jstor.org/stable/2958148). **Full text not obtained.** Publisher PDF routes failed. Bibliographic identity and the abstract-level unimodal convergence claim were checked; no precise theorem wording is attributed to an unread PDF.
- Guérin–Laulin–Raschel–Simon, [author manuscript](https://arxiv.org/html/2409.06836). **Read relevant portions, not the entire article in this pass:** introduction, complete unimodality proof, mixture conjecture, and the near-one expansion of the moment-growth constant. Their tail results take the spatial argument to infinity at fixed memory. They do not state the proposed near-one Landau profile.
- Trinas and Valle, *A Superdiffusive Local Limit Theorem for the Elephant Random Walk and the Breakdown of Log-Concavity*, [full author manuscript](https://arxiv.org/html/2609.14753v1). **Read the full mathematical text in this pass.** Their uniform local limit takes time to infinity at fixed memory. Their near-one moment calculation gives variance and third-central-moment asymptotics; it is not a near-one density profile or modal expansion. Their use of Boos's uniform-convergence criterion requires common Lipschitz bounds, which are not supplied uniformly as memory approaches one.
- Boos, *A converse to Scheffé's theorem*, Annals of Statistics 13 (1985), 423–427, [NCSU repository copy](https://repository.lib.ncsu.edu/server/api/core/bitstreams/4c94a3a3-6c4c-4e4b-9e7b-9b7c52e845bf/content). **First-page indexed text read; full text not obtained in this pass.** Both repository download routes return a bot-detection page to the research tool. Page 423 states the Ascoli/equicontinuity strategy and begins Lemma 1. No precise claim about its full hypotheses is attributed to unread pages.

### Inferences

The result should not be advertised as a new general unimodal convergence theorem. Its important feature is a new sharp description of the two ERW peaks as memory tends to one, proved by combining an existing weak bridge with the newly established curvature structure. Fixed-memory local limits and fixed-memory tail asymptotics do not imply it without a uniformity argument.

### Gaps

The Hettmansperger–Klimko full text remains an unfinished source check. A library copy would permit a precise historical comparison. The proof strategy here does not require relying on its exact wording, because the needed implication can be proved directly from interval averages.

## Can the inflection points be located as well?

### Takeaway

Yes, provided the known two-inflection structure of the Landau density is taken from the stable-density bell-shape theorem. The same fixed midpoint witnesses can localize the two rescaled positive-hump inflections without requiring convergence of derivatives.

### Cited Findings

- Kwaśnicki, *A new class of bell-shaped functions*, Transactions of the AMS 373 (2020), 2255–2280, [DOI](https://doi.org/10.1090/tran/7825), [author preprint](https://arxiv.org/html/1710.11023). **Introduction and theorem statements through Corollary 1.3 read; full proof not read.** Corollary 1.3 explicitly includes every stable distribution on the real line. The paper also explains why an older purported proof was incomplete, making this the appropriate modern source.
- Kwaśnicki and Simon, *Characterisation of the class of bell-shaped functions*, [author manuscript](https://arxiv.org/html/1910.07752). **Opened, not yet read in full.** This is broader background; the preceding article is the direct source for stable densities.

### Inferences

Let `α_L<λ_L<β_L` be the Landau inflections. In the positive ERW hump let `d1<c<d2` be the inner and outer inflections. The proposed limits are

`(Aε−d2)/(2ε)→α_L`, `(Aε−d1)/(2ε)→β_L`.

For any proposed endpoint error, choose a fixed triple in a region where the limiting curvature has the opposite sign. The profile curvature partition would force the wrong midpoint inequality on that triple. Its limiting values contradict this. Strict convexity and strict concavity, rather than derivative values or simplicity of zeros, suffice.

### Gaps

This inflection-migration extension has not yet been formalized. Before adding it to the manuscript, read the direct bell-shape source in full and verify its application to the paper's normalization of the maximally skewed index-one stable law.
