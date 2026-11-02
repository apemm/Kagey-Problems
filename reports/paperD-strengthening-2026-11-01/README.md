# Paper D bias and profile verification

This revision adds three linked results in four journal pages. The journal
manuscript has 51 pages and the extended version has 70. Both upload archives
were rebuilt from the revised sources. An isolated build reproduces the PDF
text, all package bytes match their source files, the review extract matches
Section S6, and the PDFs use embedded fonts with no Type 3 fonts. The TeX logs
have no undefined references, undefined citations, or overfull boxes.

The full Lean build and axiom audit passed: **353 modules and 23,777 theorem/lemma
declarations**, with no unimported files. This is 22 modules and 139 declarations
more than the preceding audit. Every declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`, or a subset of them. There were 24 linter
and deprecation warnings and no build errors. All 353 source hashes were checked
again after the audit and still matched. `final-state.json` also records that
the 14 reviewed threshold source/data files match commit `b3fe997` byte for byte.

## Mathematical changes

| Result | Manuscript | Final Lean declaration |
| --- | --- | --- |
| At most two finite modal plateaus, for every bias and every nondegenerate reversal probability | Proposition F.5 | `Kagey131.PaperD.BiasedModes.diff_signPattern`; `no_four_increments` gives the corresponding interval statement |
| At most two local maxima of every biased superdiffusive density | Theorem 4.6 | `Kagey131.PaperD.Modes.biased_limit_modes_of_smoothing` |
| Entire density extension for every bias | Lemma F.4 | `Kagey131.PaperD.Modes.biased_entire_extension_of_smoothing` |
| Uniform Landau profiles, fair peak positions/heights, and total variation approximation uniformly over bias | Theorem 4.7 | `Kagey131.PaperD.Modes.near_one_profiles_of_probability_bridge` |
| Exactly two local maxima at sufficiently high memory, with uniform positions and weighted heights for biases bounded away from 0 and 1 | Corollary 4.8 | `Kagey131.PaperD.Modes.NearOneProfileConclusions.biased_modes` |

The finite theorem uses the actual conditional count recurrence and no external
probabilistic theorem. It includes both boundary histories and deterministic
first-step biases. The literal sign-pattern theorem is stronger than counting
strict maxima in a finite numerical grid.

The limit theorem takes the span-two lattice local limit as an explicit input.
The scale is `N^a / 2`, at `floor((N + N^a x)/2)`. Trinas and Valle's Theorem 3.1
was checked in full mathematical context. The Fourier smoothing inequality and
density representation are explicit inputs from the conditional limit law;
analyticity and absence of flat intervals are conclusions.

The profile theorem takes the existing weak bridge as convergence of probability
measures with their actual scaled densities. Portmanteau gives interval masses.
The new proof derives off-mode convergence, controls the height through the
proved fair curvature partition, and obtains uniform convergence and L1
convergence. It uses the published conditional unimodality, standard Landau
density facts and the existing Landau mode certificate. The old martingale
proof of the weak bridge is still not formalized. The final biased corollary
derives its mode-count and no-flatness inputs; it does not assume two modes.

The earlier total variation coupling upgrade and threshold certificate also
retain their previously documented formalization limits. No transition-uniqueness
or centred-interval theorem for bimodal biases was added.

## Source and presentation review

The new finite and profile proofs received an independent written review.
The count-law notation was disambiguated for biased starts, reflected difference
superscripts were corrected, and the L1 claim was written as an explicit density
approximation. Seven PDF pages covering the title page and new results were
rendered; the theorem and formula layouts were inspected.

The source-reading and novelty record is in
[Paper D transition and modes](../Paper%20D%20transition%20and%20modes.md).
The generalized-binomial full-text comparisons remain incomplete. The manuscript
therefore makes no categorical claim of priority for the finite theorem.

The existing disclosure was preserved. Its normalized UTF-8 SHA-256, including
the section heading and ending immediately before Statements and Declarations,
is unchanged from source commit `bad52c418826023ac12a971365e714e7483108a9`:

```text
ed20652c6d4be4b2b4eab60960d73bbd0a1b1487f596bd7a8de6fb506288593d
```

## Reproduction

`run_verification.py` calls the existing full Paper D verifier. It checks the
root import closure, builds the library, compares the source declarations with
Lean's declaration inventory, and checks every theorem's axioms. Its output
files are `build-log.txt` and `verification-manifest.json` in this directory.

```text
python run_verification.py --workspace C:/Users/arjun/lean-work/paperD --toolchain C:/Users/arjun/.elan/toolchains/leanprover--lean4---v4.33.1/bin
```

The executable paths above describe this machine. The project uses Lean 4.33.1
and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`.
`check_final_state.py` rechecks source hashes, disclosure preservation and release
references. `run_release_numerics.py --commit <sha>` exports the specified commit
to an isolated directory and runs the six-script numerical suite there, keeping
generated numerical output out of the manuscript worktree. Its record states
the source commit, dependency versions and precise scope of the threshold checks.
`integrate.py` records the initial proof-fragment insertion; subsequent review
edits are in Git. It is not a manuscript generator and should not be used to
overwrite a later revision.
