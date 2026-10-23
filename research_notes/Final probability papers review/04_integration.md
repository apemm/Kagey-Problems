# Final integration and verification

The D, F and E edits follow the supplied plan, with source-verifiable citation repairs.
The C revision implements the requested opening, scope, provenance and cover-letter changes.
The research report and the original reviewer notes distinguish completed fixes from audit limits.

| Manuscript | Final build | Main changes |
|---|---|---|
| D | 41 pages, 12-page Online Resource, 53-page combined preprint | Bulk-first abstract, early Bokes comparison, rewritten opening and heuristic, shorter verification section, coverage tables indexed from the Lean map, disclosure and cover letter. |
| F | 31 pages | Golden-ratio title, shorter urn consequences and repeated discussion, open questions, dated-draft citation checks, disclosure and immutable code reference. The approximate 29-page target was not achieved. |
| E | 25 pages | 225-word abstract, disclosure within Acknowledgments, existing shared-code and Lean-map fixes retained, unused unpublished C comparison removed, immutable code reference. |
| C | 64 pages and 14-page proof supplement | Theorem A near the top of page two, followed by the K4 envelope. Novelty and scope paragraphs are also on page two. Iltis and unpublished E omitted, Kim–Landim updated, two referee precision fixes applied, disclosure and cover letter revised. |
| 001 | Both versions 36 pages | Sections 2, 3 and 8 clarify conventions, strip symmetries and the finite-automaton/bounded-excess argument. The expanded disclosure records the first draft, October shortening, figures, checks, LRAT/Lean work, literature and later reviews/revisions. |

The first two C pages were rendered and inspected. Theorem A starts about 14 percent down page two. The four-state analytic figure remains unchanged mathematically and now appears immediately after it. The local law is compared with earlier local-time theory without claiming that densities, exact ranges or large deviations are new.

## Citation outcomes

- D's Bokes–Hlubinová–Singh model identification, Eqs. (6)–(10) and Eqs. (58)–(60) were checked against the published paper. The exact center coefficient and the pre-existing Landau approximation are credited.
- All seven Engländer–Volkov locators were checked in the public author draft dated March 18, 2024. The published edition's internal numbering was not verified. F identifies the draft in a text footnote and uses its locators there, while its bibliography lists the published monograph. The first family in draft Section 5.7 has a factor-of-two normalization discrepancy. F uses its own averaging proof.
- DLS's Theorem 2.18 is version-pinned to arXiv v1. Its finite-time count marginal is distinguished from the joint count/last-state extension.
- The numbered A inputs in D/E match the current A map, including Theorem 3.3(i), Corollary 3.7(b),(c), Proposition 3.8 and Proposition 4.1.
- Kim–Landim's 2025 publication metadata is recorded, with Lemma 5.7 explicitly located in the inspected arXiv v2.
- E's Ashkin–Teller decoupling follows from its displayed weight, so no unverified optional Baxter locator was added.

## Mathematical audit and preservation

The independent C audit checked the central model, support-selection, killed-face local-law, whole-face maximum and crossing arguments, with selected weak-field and next-order steps. It found no theorem-invalidating defect in that inspected chain. It found one incorrect unrestricted probability interpretation of the variational functional, now restricted to (H), and recommended describing the maximizing displacement as that of the quadratic model, now done. This is an internal referee-style review, not external peer review or full certification.

All 53 D, 19 F, 13 E and 47 C theorem/lemma/proposition/corollary/conjecture statement blocks are unchanged after whitespace normalization. Their explanatory prose and specified proof exposition were revised. No Lean proof file was changed and no Lake build or expensive numerical sweep was run. The existing formalization records remain the evidence for the unchanged Lean sources.

## Production checks

- All nine PDFs compile without unresolved references, duplicate labels, rerun requests or overfull boxes. Benign underfull boxes and package notices remain recorded in the build JSON files.
- The D/F/E abstracts count as 221/208/225 words when each inline formula counts as one word. This leaves margin under JTP's 150–250 range and IOP's normal 300-word ceiling.
- 001's comment-free single-file export matches the expanded multi-file sources. Both PDFs have identical extracted text.
- Saved manuscript sources match the inputs used for the isolated builds. Visual checks cover the revised sections, disclosures, front matter and page contact sheets.
- The immutable implementation revision is recorded after the source commit, and the availability links and affected PDFs are rebuilt in the final pin commit. No release tag is invented, and nothing is submitted to a journal or arXiv here.

The adjacent `validation` directory contains compact build and preservation records. External full-text PDFs and page images stay local; the public source register gives their original URLs and hashes. The unrelated working change in `kagey-problems/lean/README.md` is excluded from the commits.
