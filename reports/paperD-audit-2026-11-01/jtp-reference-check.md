# Paper D: Journal of Theoretical Probability reference check

Checked 1 November 2026. This report distinguishes the journal's stated requirements from examples of its editorial practice. The reference audit informed the manuscript's final formatting edits; this report records the evidence and the remaining author checks.

## Recommendation

Retain the six relevant public arXiv references, accurately identified as preprints, and retain the published versions already recorded for Guérin–Laulin–Raschel, Guérin–Laulin–Raschel–Simon, Althaus–Hartung–Steiner and Gut–Stadtmüller. Current JTP articles demonstrably include public arXiv references. This is evidence of practice, not an express exemption from the restrictive wording in the submission guidelines.

The unposted `arxivD` bibliography placeholder has been removed. The journal instead points to the extended manuscript supplied for review. If a public identifier is assigned before submission, add the actual identifier and rebuild. Do not describe an unpublished manuscript as accepted.

## Stated requirements

The official [JTP submission guidelines, References](https://link.springer.com/journal/10959/submission-guidelines#Instructions%20for%20Authors_References) require numbered citations in square brackets, consecutive bibliography numbering, cited works only, and published or accepted works in the bibliography. The exact eligibility phrase is “published or accepted for publication”; unpublished work and personal communications are assigned to the text. The same section asks for available DOIs to appear as full DOI links. It gives an online-document example and asks for standard journal abbreviations, allowing the full journal name when the abbreviation is uncertain.

The examples use surname followed by initials, a colon before the title, and the year at the end. Matching that punctuation is a sensible consistency edit. The explicit requirements above are stronger than any inference drawn from example punctuation.

## Public preprints in current JTP articles

These are primary publisher pages, not third-party summaries. I read the relevant bibliography entries and publication metadata, not the entire mathematical texts for this task.

| JTP article | Publication | Public-preprint reference in its bibliography |
| --- | --- | --- |
| [Althaus, Hartung and Steiner, *A Random Walk Approach to Broadcasting on Random Recursive Trees*](https://link.springer.com/article/10.1007/s10959-026-01519-z) | 30 June 2026; volume 39, article 65 | Reference 20 cites Addario-Berry et al., *Optimal root recovery for uniform attachment trees and d-regular growing trees* (2024), as arXiv:2411.18614. Reference 42 cites Guérin et al.'s fixed-point paper as arXiv:2308.14630. |
| [Gut and Stadtmüller, *Bernoulli Elephant Random Walks*](https://link.springer.com/article/10.1007/s10959-026-01517-1) | 3 June 2026; volume 39, article 60 | Reference 12 cites Maulik, Roy and Sadhukhan, *Asymptotic properties of generalized elephant random walks*, as arXiv:2406.19383 (2024). |

These examples establish that an arXiv entry is not automatically excluded in JTP's published practice. They do not establish whether each cited manuscript was already accepted elsewhere when the JTP article was processed. In particular, the fixed-point paper now has a journal publication, which Paper D already cites. Keeping the preprints with transparent status is preferable to losing needed attribution; eligibility remains subject to the handling editor's interpretation.

## Status of Paper D's six public preprints

I checked all six primary arXiv abstract/metadata pages and ran exact-title searches for possible publisher versions. No journal reference, acceptance statement, or publisher version was found in this check. This is an absence of confirmed publication information, not proof that none has been accepted. Preserve the current `preprint, 2026` status until a primary source establishes an update.

| Bibliography key | Primary record checked | Latest version information visible in this check |
| --- | --- | --- |
| `tv2026` | [Trinas and Valle, arXiv:2609.14753](https://arxiv.org/abs/2609.14753) | Submitted 13 September 2026; v1 |
| `muraharatokumitsu2026` | [Murahara and Tokumitsu, arXiv:2610.35019](https://arxiv.org/abs/2610.35019) | Submitted 26 October 2026; v1 |
| `vishwakarma2026` | [Vishwakarma, arXiv:2609.11035](https://arxiv.org/abs/2609.11035) | Submitted 10 September 2026; v1 |
| `paperA` | [Pemmasani, arXiv:2610.06935](https://arxiv.org/abs/2610.06935) | Submitted 3 October; revised 17 October 2026; v3 |
| `fanqi2026` | [Fan and Qi, arXiv:2610.16065](https://arxiv.org/abs/2610.16065) | Submitted 12 October 2026; v1 |
| `ksw2026` | [Kardas, Shneer and Wachtel, arXiv:2606.22960](https://arxiv.org/abs/2606.22960) | Submitted 22 June 2026; v1 |

The displayed authors and titles agree with Paper D's entries. The titles in the table links are abbreviated to author names only for readability; no title change is recommended.

## Local reference audit

Files read: `kagey-problems/problem131/paperD/problem131_memory.tex` and `online_resource_bib.tex`. This was a complete read of their bibliography entries. It was not a fresh verification of the mathematics or every published article's metadata.

1. The manuscript uses a numbered `thebibliography` list and numeric `\cite` commands, consistent with JTP's citation scheme. The final compiled-build check must confirm that each entry is cited in that build; the journal and combined arXiv builds include different material.
2. The audit requested full `https://doi.org/...` link labels as well as full URL targets, including Hoeffding's entry in `online_resource_bib.tex`. Verify this in both final PDFs after the formatting edits.
3. The `arxivD` item, which formerly said “arXiv number to be added,” has been removed together with the dangling citation. The journal-mode `\arxivonly` macro and the further-results paragraph now refer to the supplied extended manuscript.
4. Kagey's online problem includes an access month and year; DLMF includes a release identifier. An exact access date may be added after reopening the actual source. Do not invent an earlier access date. The guideline's dated online-document example supports consistency but does not specify mandatory day-level precision.
5. The published records already used for the fixed-point paper and the two 2026 JTP papers should not be reverted to their preprint versions.

## Scope and remaining limits

Read for this check: the official References section in full, relevant publisher bibliography entries and metadata for the two JTP examples, all six arXiv metadata pages, and both local bibliography files. The exact-title searches found no confirmed publication upgrades. The full mathematical texts of these six preprints were not reread for this formatting check; their earlier reading scope and novelty findings are recorded separately in `literature-review.md`.

No external access blocker remains for this reference check. The unposted self-reference has been resolved without inventing an identifier. The public-preprint policy tension remains an editorial interpretation, documented here with direct evidence. The author should confirm that every cited source has been read before approving the manuscript's reading statement.
