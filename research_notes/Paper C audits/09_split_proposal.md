# Paper C audit 09: the split, for the author to decide

October 24, 2026. The paper is not split in this revision. This note puts the two proposals of the
reviews side by side, so that the decision can be taken later. Page counts are article build
(`problem131_chains.tex`), with the Springer build (`problem131_chains_sn.tex`) in brackets.

Where things stand. Before the revision of October 24 the builds had 100 (109) pages. After it they
have 95 (104). The cuts made are listed in the README of `paperC`. Both reviewers asked for a split,
the editor (report 06) as the preferred option with a single paper of at most 70 article pages as
the alternative, and the referee (report 07) as a request, with 50 to 60 pages as the bound for a
single paper. The present 95 pages are above both bounds.

The logical line is the same in both proposals. Sections 9 and 10 use only the first-order scores
with a field (Remark `rem:first-field`, Proposition `prop:controlled-score`) and the face maxima
(Theorem `thm:facemax`, Proposition `prop:uniform-facemax`). Nothing in Sections 5 to 8 depends on
Sections 9 and 10. Only Theorem `thm:finite-horizon` and part (f) of Theorem `thm:nonreversible`
use the second-order theory.

## Proposal of report 06 (editor): two papers

### Paper C1, "Occupation counts of rarely switching Markov chains: a stratified local law, crossings and the boundary layer"

| Section | Content (labels) | Article pp. | sn pp. |
|---|---|---|---|
| 1 Introduction | Theorems A, B, C, the layer in prose, related work (Good, Pedler, Herve and Ledoux, Kontoyiannis and Meyn) | 4 | 4.5 |
| 2 Setting and the exact law | `def:faces`, `lem:admissible`, `lem:runs`, `lem:continuum`, `fig:simplex` | 3.5 | 4 |
| 3 The rate on a face | `prop:restriction` (as a remark), `lem:face-monotone`, `prop:rate`, `prop:variational` | 3 | 3.5 |
| 4 First-order face selection | `lem:upper`, `thm:first`, `thm:hull`, `fig:cycles`, the 4-cycle as a paragraph | 3.5 | 4 |
| 5 The local law, face maxima, crossings | `def:tilt`, `prop:constant`, `cor:symface`, `thm:local`, `thm:stratified`, `thm:facemax`, `thm:crossing`, `thm:window`, `lem:weighted-cayley`, the reducible face as a short remark | 8 | 9 |
| 6 The boundary layer at a facet | `lem:layer-exact`, `lem:layer-exact-discrete`, `prop:pair-face`, `prop:layer-constants`, `prop:layer-prefactor`, `hyp:L`, `lem:L-two`, `thm:layer` | 8 | 9 |
| 7 The complete graph | `prop:pair`, `cor:paperA`, `cor:paperB`, `thm:simplex-crossing`, `thm:simplex-balance`, `cor:simplex-modes`, `fig:complete-envelope`, start and weak field as remarks | 5 | 5.5 |
| 8 Near a vertex | `thm:vertex-uniform-root` and its link to Section 6 | 1.5 | 1.5 |
| 9 Open questions, computations | one paragraph each | 1 | 1 |
| App. A | local law and first-order bounds, without the forest formula | 7.5 | 8 |
| App. B, C, D | Laplace lemma, complete graph, near a vertex | 6 | 6.5 |
| References | | 2.5 | 3 |
| Total | | about 53 | about 59 |

### Paper C2, "Which coarse functionals of the occupation law determine a Markov generator?"

(Alternative title: "The Donsker and Varadhan functional, principal minors and modal supports of
finite Markov chains".)

| Section | Content (labels) | Article pp. | sn pp. |
|---|---|---|---|
| 1 Introduction | the question, Theorem D (the DV fiber and the generator fiber), Theorem E (reversible design), Theorem F (cycles from depths), borrowed versus new | 3.5 | 4 |
| 2 Setting | the killed functional, the variational formula, `prop:controlled-score`, citing C1 for `thm:first` and `thm:facemax` | 3 | 3.5 |
| 3 The DV functional and principal minors | `lem:RF-irreducible`, `lem:perron-branch`, normalization (N), `thm:nonreversible`(b)-(e), `cor:dv-fiber` as a theorem, the cut-transpose example | 5.5 | 6 |
| 4 Reading the minors from modal supports | `lem:suppression-nr`, `lem:exposure`, `thm:nonreversible`(a), (f) | 4 | 4.5 |
| 5 The reversible design | `lem:suppression`, `thm:reversible-reconstruction`, `thm:minimality`, `thm:stability` | 4.5 | 5 |
| 6 Finite horizons | `prop:uniform-facemax` (only the uniformity argued), `thm:finite-horizon` | 3 | 3.5 |
| 7 Low temperature | `thm:depth`, `thm:noncritical`, `prop:prefactor`, `thm:critical-window`, `ex:four-state`, `ex:branch-switch` | 6 | 6.5 |
| 8 Reading the cycle tree | `prop:unperturbed`, `lem:laminar`, `lem:killed-depth`, `lem:nested`, `thm:attraction`, `thm:cycles-from-depths`, `thm:window-prefactors`, suppression in one paragraph | 4 | 4.5 |
| 9 Open questions, computations | | 1 | 1 |
| References | | 2.5 | 3 |
| Total | | about 37 | about 41 |

The editor's reasons: one referee pool per paper, a one-way dependence (C2 cites C1 as a
preprint), different methods, so not salami slicing. A single paper would have to drop whole
results to reach 70 pages (finite horizons, the near-vertex law, start and weak field, window
prefactors).

## Proposal of report 07 (referee): two or three papers

| Paper | Content | Length | Venue suggested |
|---|---|---|---|
| 1 | Sections 2 to 5, Section 6 restricted to faces with at most three states (the case of four or more as a conjecture), Section 7, Appendices A to C. Section 3 cut to about 2 pages. Section 8 and Appendix D go. | (not given; Sections 2 to 7 minus cuts, roughly 45 to 50) | JTP |
| 2 | Section 9.3 with Corollary `cor:dv-fiber` and the minimal parts of 9.1 and 9.2: the DV-functional fiber with the cut-transpose translation | 12 to 15 | ECP or a probability and linear algebra venue |
| 3 (optional) | the reversible design with stability and finite horizons, together with Section 10 | 20 to 25 | |

The referee's single-paper alternative (about 70 pages after 28 to 30 pages of cuts) is in report
07, Section 6. Of its cuts, the revision of October 24 made the 4-cycle, the flows and next-term
remarks, the route to Hypothesis L and the layer heuristics and numerics, part of the start
subsection, the suppression block and most of the verification section. It did not make: Section 3
to 2 pages, the forest formula to a statement only, deleting Section 8 and Appendix D, merging
Proposition `prop:controlled-score` with Remark `rem:first-field`, Theorem `thm:minimality` to a
remark, Remark `rem:finite-size`, Lemmas `lem:laminar` and `lem:nested` to citations, and Example
`ex:branch-switch`.

## Points to decide

1. One paper of about 95 pages, two (06), or two or three (07).
2. If two: whether Section 8 (near a vertex) stays in C1 (06 keeps it, 07 drops it), and whether
   C1 keeps Theorem `thm:layer` for four or more states under Hypothesis L (06) or states that case
   as a conjecture (07).
3. If C2 is separate: whether the low-temperature half goes with it (06) or with the reversible
   design in a third paper (07), and whether the DV fiber alone is a short note (07) or the lead
   theorem of C2 (06).
4. In every case the cover letter and the companion statement change, since the present letter
   describes one paper that incorporates arXiv:2610.09258.
