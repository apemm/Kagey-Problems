# Paper D headline proof audit

This audit covers Theorem 4.4, Section S6.D, Theorem 4.6 and Propositions
F.5--F.6 after their addition to the manuscript. The
[direct proof review](../../research_notes/Paper%20D%20headline%20audit/primary_review.md)
records the derivations, source-reading scope and findings.

The main improvement is a weaker dependency for Theorem 4.6. Lemma F.7 uses
ordinary weak convergence and lattice-window averages to transfer the finite
shape inequalities. The theorem no longer requires the Trinas--Valle local
limit. The manuscript retains that result as an alternative and explicitly
identifies its source as an unrefereed arXiv preprint.

## Formal coverage

The new entry `Modes.biased_modes_centered_interval_of_weak_probability`
starts with the actual scaled atomic laws, their weak convergence and the
limiting density. It computes interval probabilities, applies Portmanteau,
normalizes the lattice counts and transfers the forbidden valley patterns.
Conditional unimodality and the characteristic-function smoothing/Fourier
inputs remain explicit. No pointwise local limit or limiting shape is assumed.

For the transition, the additions check the smoothing chain and product
derivatives, the varying mixing weight, dominated integral differentiation,
half-interval reflection, both weighted scalar forcing integrals, the
differentiated geometric remainder and the Fourier power-tail bound.
The earlier formal assembly proves uniqueness and the critical unimodal case.

The full transition certificate is not a Lean proof. The characteristic-function
instantiation, holomorphic moment/Cauchy estimates and assembly of the uniform
tail bounds retain their written analytic proof. Arb's transcendental
enclosures remain numerical. Section 5 states these boundaries explicitly.
The statement map is in `kagey-problems/problem131/lean/PaperD/MAP.md`.

## Numerical and document checks

The fresh 1,600-bit run with 1,100 moments passed all 19 derivative-certificate
checks under `python -O`. It gives `0.68 < d/da g_a''(0) < 0.70` and
`-0.09 < g_a''''(0) < -0.07` throughout the stated neighbourhood.
The numerical proof sources and original reviewed threshold records were
not changed.

The journal manuscript is 52 pages, the extended version is 73 pages, and
the threshold review extract is 9 pages. The added page contains the weak
transfer proof. The abstract and all headline statements remain unchanged.
The rebuilt PDF identifies the preprint on page 24 and explains the formal
boundaries in Section 5. The upload archives include the revised sources.

`verification-manifest.json` records the complete Lean source inventory,
declaration count and axiom audit. `final-state.json` checks those source hashes
and the release references. It also compares the complete module inventory and
every source with the pinned commit. The sole permitted checkout conversion is
Git's LF-to-CRLF conversion, recorded per file and checked against Git's clean
filter. `pdf-checks.json` checks isolated PDF builds,
font embedding, references and the exact archive contents. The final
`release-verification.json` joins the checks for the immutable source tag.

## Reproduction

Use Python 3.12 with `numpy`, `scipy`, `mpmath`, `python-flint`, `pypdf` and
`pypdfium2`; Lean 4.33.1; and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.

```text
python reports/paperD-headline-audit-2026-11-01/run_verification.py --workspace C:/Users/arjun/lean-work/paperD --toolchain C:/Users/arjun/.elan/toolchains/leanprover--lean4---v4.33.1/bin
python reports/paperD-headline-audit-2026-11-01/run_release_numerics.py --commit paperD-arxiv-v3
python reports/paperD-headline-audit-2026-11-01/verify_release_build.py --commit paperD-arxiv-v3 --workspace C:/Users/arjun/lean-work/paperD --toolchain C:/Users/arjun/.elan/toolchains/leanprover--lean4---v4.33.1/bin
```

The numerical release runner exports the named commit before running the
seven-script quick suite. It checks the archived threshold records, runs three
fresh threshold probes and reruns the complete derivative certificate. It
does not repeat all nine original heavy threshold jobs or the full historical
center and convexity sweeps. The full Lean audit checks every current module
and declaration, including unchanged parts of the library.

The v1 and v2 tags retain their original commits. This revision is v3.
No manuscript has been submitted or posted to arXiv. A
[note for the conjecture's authors](../../research_notes/Paper%20D%20headline%20audit/posting_note.md)
is prepared for use after a public preprint link is available. It has not
been sent.
