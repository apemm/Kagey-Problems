# Paper D final manuscript and package audit

## Scope and conclusion

The review covered the abstract, all main sections, all seven appendices,
Sections S1 to S6, both extended proof files, the cover letter, metadata,
submission instructions and source archives. It checked statement ranges,
proof dependencies, endpoint cases, notation, cross-references and agreement
between the journal and extended versions. No new substantive proof gap was
found. This is a manuscript consistency review, not a new independent
formalization of the paper.

The focused mathematical checks included:

- The finite-time bias bounds, the critical density, the empty centred bias
  interval and the endpoints `q = 0, 1`. The all-bias density approximation
  is distinguished from the two-peak conclusion for biases bounded away
  from zero and one.
- The derivative certificate's analytic interface and Section S6's scaled
  and unscaled curvature bounds. The global modal-transition statement is
  distinguished from uniqueness of the curvature zero through `a = 0.6712`.
- The small-length cases, including the crossing `epsilon = 1/3` at `N = 2`.
- The family and tail estimates, weak shape transfer, dominant-half argument,
  and Section S4's likelihood, affinity, product-distance and consistency
  bounds.

The outstanding original Drezner–Farnum and Heyde full-text comparisons remain
as described in the reading record. This audit does not claim to have obtained
or read those sources. It adds no priority claim.

## Corrections

1. The argument for `b_a -> 0` now quantifies `0 < eta <= 1/2`, matching
   Corollary 4.8. The preceding unrestricted `eta > 0` wording included
   values that were not initial biases. No theorem or conclusion changes.
2. The introduction and cover letter specify unanimity in one colour.
   Its probability is the mass of one end, `E_N`; the union of the two
   unanimous outcomes has probability `2 E_N`.
3. Appendix B no longer says that the family proofs use a changing constant
   `C`. Those proofs give explicit constants.
4. Proposition S5.1 distinguishes the finite unresolved convexity range from
   the proved eventual result. It no longer suggests that all lengths above
   2000 remain untreated.
5. Seven links in the review extract previously named destinations on omitted
   pages. They now open those destinations in the supplied complete extended
   PDF. The cover explains that both files must remain together and that
   browser viewers might not support cross-file PDF links.
6. Submission notes and the Paper D README identify the current manifest.
   The shared verification supplement now records 52/72/9 pages, seven
   verification scripts, the completed formal additions and their remaining
   analytic and numerical inputs. Older result-number tables are explicitly
   identified as historical.

## Verification

Both manuscripts and the review cover were rebuilt. The arXiv source set was
then copied into an isolated directory and both manuscripts were rebuilt
there. Ordinary and isolated PDF text agrees page by page. The final counts
are 52 journal pages, 72 extended pages and 9 review pages. The abstract has
1,543 source characters.

The checks found no undefined references, undefined citations, overfull boxes
or unembedded fonts. All bibliography entries are cited. The archives have
21 arXiv files and 29 journal files, with no duplicate entries or CRC errors;
every packaged byte matches the corresponding release file. The review
extract reproduces the extended version's pages 65 to 72 after its cover.

All 397 journal and 580 extended internal links resolve. The review extract
has 26 internal links and seven links to the companion PDF, with every target
verified. This validates the PDF objects and destinations; it does not claim
that every browser viewer implements cross-file navigation.

All pages of the input PDFs were inspected at contact-sheet scale, with
full-resolution checks of the title, introduction, figures and review cover.
After rebuilding, the corrected passages and review cover were rendered and
inspected again. No clipping, overlap or layout defect was found.

The main entry source is unchanged from baseline commit `de1f05b1`.
The Lean sources, numerical programs and certificate data are unchanged from
`paperD-arxiv-v3`, which still resolves to
`9d0f4ba4995c7ec423a70463e5136056492d365c`. No numerical or Lean rerun was
needed for these wording and packaging changes. The complete prior build
and numerical evidence remains at
[commit c24791a](https://github.com/apemm/Kagey-Problems/tree/c24791af4f3a9aa0d985fce1b0a2a68f03f33432/reports/paperD-headline-audit-2026-11-01).
Section 5 retains the explicit boundaries between formal proofs, written
analytic arguments and numerical enclosures.

The compiler declaration was checked against the
[official arXiv 00README specification](https://info.arxiv.org/help/00README.html)
on November 2, 2026. The declared version, compiler and top-level/include
roles are supported. Local builds use TeX Live 2026; the arXiv submission
service itself has not been run, and nothing has been posted or submitted.

## Reproduction and records

Compile `problem131_memory.tex`, `problem131_arxiv.tex` and
`threshold_review_cover.tex` from the paper directory into
`.pdf-build/paperD-final-audit-2026-11-02`. From the repository root run:

```text
python reports/paperD-final-audit-2026-11-02/package_revision.py
```

Compile both manuscripts in `.pdf-build/paperD-final-clean-2026-11-02`
using output directory `build`, then run:

```text
python reports/paperD-final-audit-2026-11-02/check_jtp_package.py
python reports/paperD-final-audit-2026-11-02/render_pages.py
```

`delivery-manifest.json` records the files and hashes. `pdf-checks.json`
records the font, link, archive, metadata and source checks. The two build
logs preserve the compiler output. `rendered-pages.json` identifies the
final rendered pages. Earlier audit records are unchanged.
