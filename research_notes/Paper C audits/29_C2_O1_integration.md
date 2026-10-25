# 29. Paper C2, the exact occupation law integrated (October 25, 2026)

Sources: `research_notes/Paper C2 identifiability O1/01_report.md` (results, proofs, prior work)
and `02_audit.md` (all six claims proved as written, two routine steps to be written out, Lemma
1.1(iv) with N^2 D in place of N D). Starting point: the state recorded in
`26_C2_second_review_fixes.md`.

## Builds

| File | Class | Pages | Status |
| --- | --- | --- | --- |
| `paperC2/problem131_reconstruction.tex` (journal) | elsarticle, preprint 12pt | 43 (was 33) | no undefined or multiply defined references, no overfull boxes |
| `paperC2/problem131_reconstruction_arxiv.tex` (arXiv) | article 11pt | 46 (was 37) | same |

`py -I verify_all.py` passes, 6 of 6 scripts. The new section takes 8 pages of the journal build
(pages 16 to 24) and the introduction 1.5 more. The journal version is now 3 pages over SPA's
30 to 40, and the cover letter says why in 3 sentences. If the length has to come down, the first
candidates for the arXiv-only part are the proof of Theorem 4.5(iii) (the genericity witness),
Remark 4.7 (one fixed N) and Remark 4.10 (necessary conditions for balance), about 1.8 pages.

## Title

Changed to "What the occupation law of a finite Markov chain determines: time reversal, principal
minors and cycle trees". The paper now answers the question at the level of the law itself
(Theorem B), so "law" is accurate. "Time reversal" names the exact-law answer, "principal minors"
the J_V and label answers, "cycle trees" the low-temperature part. "Modal supports" left the
subtitle.

## New Section 4, "The exact occupation law" (`sec_exactlaw.tex`)

Placed where the reserved stub was, after Section 3. Statement numbers in both builds:

| Number | Label | Content | Source |
| --- | --- | --- | --- |
| Lemma 4.1 | `lem:reductions` | Laplace transform, counts of I + hQ at fixed h, stationary second moments | report Lemma 1.1(i)-(iii) |
| Lemma 4.2 | `lem:graph` | a polynomial vanishing on a real graph over an open set is divisible by the irreducible P | new, makes the audit's step 5 explicit |
| Theorem 4.3 | `thm:one-horizon` | one time gives every time and the principal minors, any start | report Theorem 1 |
| Theorem 4.4 | `thm:generic-start` | generic start gives Q | report Theorem 2 |
| Theorem 4.5 | `thm:second-moments` | d <= 4 to T^4, generic to T^5 | report Theorem 3 |
| Theorem 4.6 | `thm:stationary-law` | stationary start, d <= 4, no cut, generic; converse for Q* | report Theorem 4 |
| Remark 4.7 | `rem:one-N` | E_pi[n n^T] = N^2 D + ..., one N not enough (N = 2) | report Lemma 1.1(iv), corrected |
| Proposition 4.8 | `prop:gluing` | gluing formula, stationary law of every cut-transpose generator point | report Prop 5 and side fact |
| Corollary 4.9 | `cor:balance` | balance criterion | report text after Prop 5 |
| Remark 4.10 | `rem:balance-necessary` | first two orders, sides of 2 states | report Cor 5.1 |
| Definition 4.11 | `def:memoryless` | memoryless block | report Section 6 |
| Theorem 4.12 | `thm:memoryless` | block reversal keeps F_Q | report Theorem 6 |
| Remark 4.13 | `rem:memoryless-cut` | memoryless blocks are balanced sides | report Theorem 6 step 4 |
| Example 4.14 | `ex:five-state` | the d = 5 example with exact rates | report Cor 7 |
| Conjecture 4.15 | `conj:fiber` | Conjecture A | report |
| Conjecture 4.16 | `conj:balanced` | Conjecture B | report |

What changed against the report's proofs.

- The two sentences the audit asked for. Step 2 of Theorem 4.3 now gives the radius
  epsilon_0(v) = delta(v)/(4q) from Gershgorin and says that it is bounded below on a ball, which is
  what makes U open. Step 5 says that the vanishing holds only for real w and that Lemma 4.2 turns
  it into a polynomial identity. Lemma 4.2 does this by a resultant, so no complex continuation is
  needed. It is used three times (steps 3, 5 and 6), and step 6 replaces the partial fractions of
  the report.
- Lemma 1.1(iv) is Remark 4.7 with N^2 D, and the remark says where N^2 comes from (ND plus the
  k = 0 terms N(N - 1) D). It adds a consequence that follows from Theorem 4.5: for N >= 3 the
  laws at one N for N - 1 values of h give Q up to reversal when d <= 4. The N = 2 example is
  written with Q_k = S + kC and the remark that Q_k^* = Q_{-k}.
- Theorem 4.12 has a new and shorter proof. Solving (diag x - Q) z = 1 blockwise shows that F_Q
  depends on Q_B only through g = rho (diag x_B - Q_B)^{-1} 1, which is invariant under Q_B ->
  Q*_B. It needs neither the gluing formula nor the case split on |B^c|. The report's route is kept
  as Remark 4.13. Irreducibility of Q^[B], which the audit noted as unproved, now has a sentence.
- Proposition 4.8 is stated and proved in the coordinates of Q, with the factors of
  (eq:cut-transpose), and the generator point is identified as -E^{-1} C' E with E = diag(I_X,
  D_Y).
- Theorem 4.5(iii). The polynomial that controls the coupling is written out (the product of
  tr(P_k S P_l S) times (prod_k u_k psi'(u_k))^{r-1}).
- Example 4.14 adds a hand check that Q^[B] is not Q*: q^[B]_14 = 1 and q*_14 = 3/2.
- Not included: the claim "any d >= 5 admits such examples" (no proof was written), and the
  claim that Conjecture A is proved for single cut-transposes (only the criterion is proved). The
  text says only that the first example has d = 5 and that none exists for d <= 4.
- Conjecture B is translated to the coordinates of Q: u = D_X a, and the matrix
  (pi_i q_ij - pi_j q_ji) on X is a sum of matrices supported on memoryless blocks inside X. The
  text says which parts are proved (necessity of u = D_X a, the case X = B).

## Introduction and abstract

- New Section 1.2 "The exact law" with Theorem B (`thm:law`), stated after Theorem A and
  Corollary 1.1. Part (iv) says that time-reversal identifiability fails in general, with the
  memoryless block. The old paragraph on path reversal and amplitudes is folded into the last
  paragraph of 1.2, which states that the first level of the comparison is now answered.
- Lettering. A (functional), B (exact law, `thm:law`), C (modal supports, label `thm:B`), D (low
  temperature, label `thm:D`, now printed as D).
- Section 1.5 distinguishes the lumped-path literature for the new theorem: neither observable
  refines the other, and the obstructions differ. Ryden's order bound and Larget's equivalence
  conditions are named.
- Abstract rewritten, 234 words in the journal build, 244 in the arXiv build.

## Bibliography

Verified from Crossref on October 25: Ryden, J. Appl. Probab. 33(3) (1996) 640-653, DOI
10.2307/3215346. Fredkin and Rice, J. Appl. Probab. 23(1) (1986) 208-214, DOI 10.2307/3214130.
Larget, J. Appl. Probab. 35(2) (1998) 313-324, DOI 10.1239/jap/1032192850. Xiang, Zhou, Deng and
Yang, Chaos 34(2) (2024) 023132, DOI 10.1063/5.0156458. The Crossref abstract of the last one
says that it identifies the generator of a reversible chain, or of a class of irreversible
stationary chains, from hitting-time distributions observed at the leaves and at two adjacent
states of each cycle. So the existing sentence on hitting times is verified and the citation
stays. All four entries already had these data. The entry of Bruno, Yang and Pearson was moved to
its alphabetical place.

## Script

`paperC2/verify_exactlaw.py` (sympy, rational arithmetic, LF, about 15 s, 61 checks), listed in
`verify_all.py`, output in `data/verify_exactlaw_output.txt` with the sha256 header.

1. Example 4.14. pi, the memoryless data kappa = 3, nu = (1/3, 2/3), c = (3, 6), Q^[B] is a
   generator with law pi and differs from Q and Q*, the 31 minors, F_Q - F_{Q^[B]} = 0, Sigma_1 to
   Sigma_3, the count laws for N <= 6 at h = 1/20, the start e_1, (Q'')^* = Q^[B], and the spectrum
   of K^2 (char. polynomial t (t + 7/8)^2 (t + 3/4)^2) with P_1 S P_2 = 0.
2. The d = 4 cut example. pi = (2226, 1134, 2675, 3638)/9673, the generator point of Proposition
   4.8 reproduces q'_13 = 50/21, q'_41 = 63/34, q'_43 = 5/17, both gluing identities, neither side
   balanced, and the first separating moment 29 (w1 - w2)(w3 - w4)/9673 at n = 3, equal to
   (1/2) w^T (Sigma_1 - Sigma'_1) w.
3. Second moments for d <= 4. On 5 generators (the cut example, a sparse and a positive four-state
   chain, a three-state chain, a reversible chain) sympy solves K' D^{-1} K' = K D^{-1} K with
   K' antisymmetric and K' 1 = 0, and finds only +-K.
4. E_pi[n n^T] = N^2 D + ... by enumeration for N = 2, 3, 4, and the N = 2 and N = 3 circulation
   test of Remark 4.7.

## Other files in paperC2

`sec_minors.tex` (two pointers to Section 4), `sec_verify.tex` (the new script, the computed
numbers of Section 4, the open questions on the conjectures, all second moments and one pair
(N, T)), both top-level files (input of `sec_exactlaw.tex`, a `conjecture` environment, the
title), `README.md`, `TEMPLATE.md` (pages, abstract count, highlights), `cover_letter.md`
(Theorem B paragraph, length justification).

## Outside the write scope, now stale

Section numbers after Section 3 moved up by one (Section 5 is now 6, Example 5.5 is now 6.5,
Theorem 5.11 is now 6.11, the arXiv Section 7 is now 8), and the title changed. These files still
use the old numbers or title: `lean/PaperC/MAP.md` (C2 title, page counts, "Section 6" for the
four-state example and the C2 section list), `lean/README.md`, `problem131/README.md`,
`problem131/SUPPLEMENT.md`, and possibly `paperC/README.md`, `paperC/TEMPLATE.md`,
`paperC/EXPORTS.md`. The Lean sources need no change.

## Not done

- No new literature search beyond the bibliographic checks above. The report's prior-work section
  asked for a full reading of Ryden Sections 2 and 3, the Xiang paper and the MAP literature
  before submission. That is still open.
- Conjectures A and B, all second moments versus the law, and one pair (N, T) are open and are
  said to be open.
