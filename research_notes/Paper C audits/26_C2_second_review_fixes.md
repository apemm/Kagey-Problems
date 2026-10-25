# 26. Paper C2 after the second referee report (October 25, 2026)

Scope. Sections 3 and 4 and the length budget of `02_C2_plan_SPA.md`, and every finding of the C2
referee report of October 25 except the new theorem O1 (the exact occupation law). O1 is left to
separate work. The introduction has a marked comment where it goes, and both top-level files have
an empty stub comment for its section. Nothing about it is claimed.

## Builds

| File | Class | Pages | Status |
| --- | --- | --- | --- |
| `paperC2/problem131_reconstruction.tex` (journal) | elsarticle, preprint 12pt | 33 (was 40) | no undefined or multiply defined references, no overfull boxes |
| `paperC2/problem131_reconstruction_arxiv.tex` (arXiv, new) | article 11pt | 37 | same |

`py -I verify_all.py` passes, 5 of 5 scripts (211 s). The scripts were not changed.

## Structure

- Build switch `\newif\ifarxivbuild`, false in the journal file and true in the arXiv file. Both
  input the same section files and a shared `abstract.tex`. The arXiv file adds
  `sec_reversible.tex` as its final Section 7, after the computations. Sections 1 to 6 and all
  their statement numbers agree in the two builds. The journal version points to the arXiv
  version in one sentence at the end of Section 1.3. Entries and sentences used only by the
  reversible design (Wolfer and Watanabe, the uniform import in Section 2, the script list for
  Section 7) are inside the switch.
- Title: "What the occupation functional of a finite Markov chain determines: principal minors,
  modal supports and cycle trees". The plan says "law" becomes accurate once O1 is in. Until then
  "functional" is the honest word.
- Theorem lettering: A (functional), B (modal supports), C (low temperature, label still
  `thm:D`). The old Theorem C (reversible design) is no longer an introductory theorem.

## Task 1. The inverse problem and Kim and Landim

Verified from the full text of arXiv:2412.13515v2, Section 5:
- Lemma 5.1. The level-two functional I alone gives the exit rates and the products
  R(x,y)R(y,x), that is, the principal minors of orders 1 and 2. No irreducibility is assumed.
- Lemma 5.2. The invariant measures of the closed classes come from the zero set of I.
- Corollary 5.3. If the chain is reversible, I determines its generator.
- Example 5.4. The 3-cycle with unit rates and its reversal share I = 1 - 3(m_a m_b m_c)^{1/3}.
  They say "the DV large deviations rate functional does not characterise the dynamics if the
  chain is not reversible", and the abstract and Section 1 call the conditions optimal.
- Corollary 5.8. If every state is recurrent, the measure-current functional determines the
  rates. Example 5.9 shows sharpness with a transient state.

The introduction now runs: the inverse problem (3 resolutions), Kim and Landim and the 3-cycle,
Theorem A, Corollary 1.1 (the fiber, credited to Loewy, Hartfiel and Loewy, Al Ahmadieh and
Chatterjee, Ghosh, Gurjar and Raj), the stationary obstruction as a remark, the reserved O1 comment,
the labels (Theorem B), the low temperature (Theorem C), related work and the plan.

- Theorem A states only part (i), with the agreement of every lambda_F and J_F.
- Corollary 1.1 defines the cut, the cut-transpose, the orbit and the generator point. The orbit is
  generated from -Q or from -Q^T, so the no-cut case gives {Q, Q*} (finding C2W-03). In the body,
  Definition 3.5 states both terms, `thm:nonreversible` is now a corollary, and its proof records
  that transposition commutes with cut-transposes, (C')^T is the cut-transpose of C^T with the
  factors (u, c, b, a). This is checked by inspection of the block formula.
- A(iii) is Remark 3.8 (path reversal).
- The matrix statements were checked as follows. Al Ahmadieh (arXiv:2309.00806v2) Lemma 5.1,
  Theorem 4.1, Lemma 4.5, Lemma 6.1 and Theorem 6.2, and CGGR (arXiv:2410.01961v1) Theorem 1.1,
  Lemma 2.8, Definition 2.10 and Remark 2.11, were read in full. Loewy (1986) Theorem 1 and Hartfiel
  and Loewy (1984) Theorems 1 and 3 were not accessible, and were checked through their
  restatements in Al Ahmadieh (Lemma 4.2), CGGR (Lemma 2.8) and Boussairi and Chergui. CGGR also
  appeared in STOC 2025, pp. 1067-1078, which the entry now says (numbering cited from the arXiv
  version). Crossref lists a 2026 J. Algebra paper of Al Ahmadieh on the same subject. We could not
  confirm that it is the published version, so the arXiv citation stays.

## Task 2. Theorem C (old D)

- Mechanism. By the shift rule the reward c e^{-gamma/eta} 1_G and the killing
  -c e^{-gamma/eta} 1_{V\G} give the same winners, even at finite N. Checked against the proofs.
  Theorem 5.11(a) uses only Phi(V; v) <= d - 1 for the representative v >= 0, and the other steps
  compare differences of scores, which the shift does not change. Section 5.2 now says that both
  readings at one fixed field fail (the unperturbed path, and the killing at one large rate, which
  is the reward at the same rate), and that what works is the scan of gamma on the calibrated scale
  with the threshold readout. It explains why h > gamma is needed (otherwise every face that wins
  on the unperturbed path would have an infinite threshold). The abstract and the introduction say
  the same.
- Recast. (i) Determination, new Corollary 5.13. If two Arrhenius families with all rates
  positive have the same J_V^eta along a sequence eta -> 0, they have the same exit rates on every
  face at those eta (Theorem 3.3), hence the same depths, prefactors, cycles and cycle tree
  (Theorems 5.1 and 5.12, Proposition 5.3). The same holds for the first-order modal-support maps
  (Theorem 4.6). No reversibility and no nondegeneracy. (ii) Reading, Theorem 5.11, a design fixed
  in advance, now presented as the point of the theorem (finding C2W-04). (iii) The cycle
  criterion, Theorem 5.12.
- Hypotheses in the headline (C2W-05). Positive rates, the order of limits (N first, then eta),
  the known eta, and a one-sentence definition of "wins" are in Section 1.3 and the abstract.
  Remark 5.15 lists the calibrated quantities, the temperature included.
- Comparison paragraph, Section 1.3. Verified from the full texts. Landim (SPA 165 (2023),
  arXiv:2209.11532) and Bertini, Gabrielli and Landim (AAP 34 (2024), DOI 10.1214/24-AAP2051, arXiv
  2207.02588, reversible for the large deviations part) assume rates with a limit R_0 that is
  positive on some edge and comparability of products of rates. Kim and Landim (2.5) is the same
  comparability for the measure-current functional. Pure Arrhenius rates satisfy it after a
  rescaling of time by exp(min V/eta), since every ratio of products is e^{-b/eta}. The paper says
  so and claims no weaker hypothesis. Their expansions give the metastable states and wells on each
  time scale and the reduced chains. We add the depth of every face, the cycle criterion and the
  readout.
- Catoni (1999), read from the numdam PDF. Definition 4.2, Propositions 4.2, 4.4, 4.6 and 4.11 and
  Definition 4.3 are as cited. Correction: Proposition 4.18 is the level-set construction of
  cycles, not strict growth of depth. The text now says that strict growth can be deduced from his
  Propositions 4.5 and 4.10, and keeps our own proof (Lemma 5.10). The cycle criterion was not found
  in Catoni Section 4 or in Cirillo, Nardi and Sohier Sections 2 and 3 (their Proposition 3.2
  characterizes cycles by communication heights, and Remark 3.4 gives weak monotonicity of depth).
  Trouve (1996) was not accessible. The paper states the novelty only that far.

## Task 3. Length

- Theorem C (reversible design, dimension count, stability, finite horizon) is in the arXiv
  version only. In that section: minimality is now Proposition 7.3, "the dimension count"
  (C2W-10). The remark on the start now says how the start enters the pair entries through
  log(K_ij/mu_i) (C2W-09). The constant U is renamed tau_max (C2W-12). Proposition 7.6 notes that C1
  now proves it for any compact set of fields, that our b is C1's w_*, and our S its S_V.
- Section 4 (Theorem B) is condensed by about 2 pages. Proposition 4.6 (identifiability) is merged
  into Theorem 4.6, the proofs of suppression and exposure are shorter, and the section opens by
  saying that the modal support is an artificial observable.

## Task 4. Hygiene

- W_Q and the label (C2W-01). Section 4.1 defines the finite-horizon label W_N(omega) and the
  first-order map W_Q, Lemma 4.2(b) relates them, and "exactly" is said for W_Q only. The Section 6
  question is restated for W_N.
- Amplitudes (C2A-01). Proposition 3.9(b) is now pairwise, with Z the union over ordered pairs of
  distinct members. The proof applies the same argument with each member as base point, which is
  valid since every member is irreducible and has the same fiber.
- Perron vector at a field (C2A-02). Proposition 2.7 is cited to C1 Propositions 3.3 and 5.2, with
  the one-line argument. u = r gives the value lambda_F(v) + v.alpha*, which is J_F(alpha*) by C1
  Proposition 3.3(a), and uniqueness is C1 Proposition 3.3(b). The C1 numbers were checked against
  `paperC/EXPORTS.md` (October 25) and the current C1 source (`prop:rate` is Proposition 3.3).
- Other imported pointers (C2W-11). Lemma 2.1 now gives the part mapping to C1 Lemma 2.2(b), (c).
  Definition 2.6 deletes the row and column of state 1. Theorem 2.5 says that the field forms are
  C1 Remark 4.3.
- C1 citation (C2W-08). arXiv:2610.09258v2, "cited with the numbering of version 2. Version 1 of
  this identifier is a different paper."
- "No proof rests on a computation" (C2B-03). The proof of Example 5.5 now gives all cofactors of
  -Q_123 and -Q_124 by hand. They were checked in exact arithmetic. Section 6 now says that every
  statement is proved, and that only the explicit numbers of the cut-transpose example (and of
  Remark 7.9 in the arXiv version) were computed.
- Aggregated chains and hitting times. Cited and distinguished in Section 1.4: Fredkin and Rice
  (JAP 23 (1986)), Ryden (JAP 33 (1996), the paper on aggregated chains, MMPPs and phase-type
  laws), Larget (JAP 35 (1998)), Bruno, Yang and Pearson (PNAS 102 (2005)), and Xiang, Zhou, Deng
  and Yang (Chaos 34 (2024) 023132). Bibliographic data verified from Crossref. The content of these
  entries was checked from abstracts only, so the paper says no more than what they observe and
  that they give canonical forms or identify the generator from hitting times.
- Notation (C2W-12). lambda_F^eta for the unperturbed exit rate at temperature eta, beta(C) for the
  boundary height, epsilon for the tolerance of Lemma 4.4.

## Task 5. Lean

The modules PrincipalMinors, GeneratorFiber, DVRestriction and CriticalWindow exist and are
imported by `lean/PaperC.lean`. `verify_lean.py PaperC` ran `lake build PaperC` (exit 0) and the
axiom check. PaperC has 20 modules and 409 theorem and lemma declarations (was 16 and 346), no build
warnings, and every axiom set is within propext, Classical.choice and Quot.sound. The script wrote
`lean/build-log.txt` and, as it always does, `lean/verification-manifest.json`. No Lean source
was changed. `lean/PaperC/MAP.md` now records the build and the new C2 numbers (Corollary 3.6,
Remark 3.7, Section 5, Example 5.5, Proposition 5.3, Theorem 5.4). Section 6 of C2 names the four
modules and the build.

## Left open

- O1 (the exact law) is not attempted.
- The journal version is 33 pages, 3 more than the plan's 30 without O1. The new introduction and
  Corollary 5.13 account for most of the difference.
