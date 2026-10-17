# Paper D: Journal of Theoretical Probability (JOTP) submission guidelines

Retrieved 2026-10-16 from primary sources (Springer Nature Link journal pages, Springer journal policies, Springer Nature LaTeX author support, the December 2024 sn-jnl template package). Everything in quotation marks is verbatim.

Source URLs:
- [G] Submission guidelines: https://link.springer.com/journal/10959/submission-guidelines
- [S] Aims and scope: https://link.springer.com/journal/10959/aims-and-scope
- [H] Journal home (metrics, Snapp notice): https://link.springer.com/journal/10959
- [E] Ethics and disclosures: https://link.springer.com/journal/10959/ethics-and-disclosures
- [U] Snapp update: https://link.springer.com/journal/10959/updates/23187508
- [C] Call for papers (shows the Snapp article type): https://link.springer.com/journal/10959/updates/27709086
- [P] Springer journal policies (AI, preprints, peer review, citations): https://link.springer.com/brands/springer/journal-policies (the old URL https://www.springer.com/us/editorial-policies/artificial-intelligence--ai-/25428500 now 301-redirects here)
- [L] LaTeX author support: https://www.springernature.com/gp/authors/campaigns/latex-author-support
- [T] sn-jnl template package, December 2024 (`sn-article.tex`), linked from [L]
- [O] Fees: https://link.springer.com/journal/10959/how-to-publish-with-us

---

## 1. Aims and scope [S]
> "Journal of Theoretical Probability publishes high-quality, original papers in all areas of probability theory, including probability on semigroups, groups, vector spaces, other abstract structures, and random matrices. This multidisciplinary quarterly provides mathematicians and researchers in physics, engineering, statistics, financial mathematics, and computer science with a peer-reviewed forum for the exchange of vital ideas in the field of theoretical probability."

Editors-in-Chief: James Allen Fill and René Schilling [H]. The journal is hybrid. The open access APC is "£2290.00 GBP / $3190.00 USD / €2590.00 EUR", and authors choose between OA and subscription only after acceptance [O].

## 2. Submission system: Snapp, not Editorial Manager [H, U]
> "Snapp (Springer Nature's Article Processing Platform) is our new peer review platform, replacing the previous system, Editorial Manager." "This is a different account to the one previously used in Editorial Manager, so if you are submitting to the journal via Snapp for the first time, you should register a new account." [U]

Submission link: https://submission.nature.com/new-submission/10959/3 [C]. Support contact: snapp-support@springernature.com.

## 3. Article types and length
- The guidelines name no list of article types. The call for papers says to "Select article type: Research" in Snapp [C]. Published papers show the type "OriginalPaper" [H].
- **Length:** no page or word limit appears anywhere in [G]. Paper length is left to the editors.

## 4. Manuscript format and LaTeX template
- > "Manuscripts should be submitted in LaTeX. We recommend using Springer Nature's LaTeX template. The submission should include the original source (including all style files and figures) and a PDF version of the compiled output. Word files are also accepted." [G]
- > "For LaTeX submissions we encourage authors to use the Springer Nature LaTeX template when preparing a submission." [G]
- > "Please ensure you provide all relevant editable source files at every submission and revision. Failing to submit a complete set of editable source files will result in your article not being considered for review." [G]
- **Conclusion:** the template is recommended and encouraged, not required, at first submission. However, full LaTeX source plus a compiled PDF is required at every submission and revision. The old svjour3 class is not mentioned. The current template is sn-jnl (December 2024 package).
- Snapp compile constraints [L]: "If you are submitting to Snapp your files must be able to compile using pdflatex and must be compressed in .zip format." Snapp "Compiles files to PDF via TexLive 2021." Also: "Please do not use any custom fonts". The page also says to convert diacritics to TeX codes (\"a, etc.). The safest way to handle the bibliography is to paste the .bbl contents into the .tex file.
- Suggested template class line [T]: `\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}` ("Math and Physical Sciences Numbered Reference Style"). The template also offers the `referee` option (double spacing) and the `lineno` option.
- Headings: "Please use the decimal system of headings with no more than three levels." [G]
- Footnotes: "Always use footnotes instead of endnotes." Footnotes must not consist solely of a citation [G].
- Acknowledgments: "should be placed in a separate section on the title page. The names of funding organizations should be written in full." [G]

## 5. Title page [G]
Title ("concise and informative"); author names; affiliations ("institution, (department), city, (state), country"); "A clear indication and an active e-mail address of the corresponding author"; ORCID if available.

## 6. Abstract [G]
> "Please provide an abstract of 150 to 250 words. The abstract should not contain any undefined abbreviations or unspecified references."

- **Formulas:** the JOTP guidelines do not forbid them. Published JOTP abstracts contain inline TeX. For example, 10.1007/s10959-026-01532-2 (2026) has `\(\alpha \)`-stable in its abstract, along with in-text bibliographic citations.
- The template's generic placeholder says to check whether "citations, or equations are permitted", and its structured-abstract sample says abstracts "must not include ... equations or citations" [T]. That sample text is generic and does not override [G].
- Recommendation: light inline math is fine. Avoid displayed equations and \cite in the abstract. If a reference is needed, spell it out ("unspecified references" are prohibited).

## 7. Keywords and MSC [G]
> "Please provide 4 to 6 keywords which can be used for indexing purposes."

> "An appropriate number of MSC codes should be provided. The Mathematics Subject Classification (MSC) is used to categorize items covered by the two reviewing databases, Mathematical Reviews and Zentralblatt MATH, see www.ams.org/msc"

Published articles carry the label "Mathematics Subject Classification (2020)". Use MSC2020 codes with a primary code first. In sn-jnl the line is `\pacs[MSC Classification]{60xxx, ...}`, and keywords go in `\keywords{...}` [T].

## 8. Statements and Declarations (required)
- > "The following statements should be included under the heading "Statements and Declarations" for inclusion in the published paper. Please note that submissions that do not include relevant declarations will be returned as incomplete." [G, Title Page section]
- > "The above should be summarized in a statement and placed in a 'Declarations' section before the reference list under a heading of 'Funding' and/or 'Competing interests'. Other declarations include Ethics approval, Consent, Data, Material and/or Code availability and Authors' contribution statements." [G, Summary of requirements]
- > "Please note that Author Contribution information and Competing Interest information must be provided at submission via the submission interface. Only the information submitted via the interface will be used in the final published version." [G]
- Funding: "funding information ... needs to be disclosed upon submission of the manuscript in the peer review system ... Under 'summary of requirements' ... funding information should be included in the 'Declarations' section." [G]
- Data: "All original research must include a data availability statement." [G] Published JOTP wording: "No datasets were generated or analyzed during the current study."
- Author contributions: "These contributions should be listed at the separate title page." [G] They are also entered in Snapp.
- The "Compliance with Ethical Standards" section (human/animal subjects, informed consent) applies "if applicable". For pure probability it is not applicable.
- The heading wording is inconsistent between "Statements and Declarations" and "Declarations". The sn-jnl template uses `\section*{Declarations}` with the subitems Funding; Conflict of interest/Competing interests; Ethics approval and consent to participate; Consent for publication; Data availability; Materials availability; Code availability; Author contribution [T].
- Sample sentences from [G]: "The authors did not receive support from any organization for the submitted work." / "The authors have no competing interests to declare that are relevant to the content of this article."
- If a single author is unfunded, a minimal block could look like this:
  ```
  \section*{Statements and Declarations}
  \bmhead{Funding} No funding was received for conducting this study.
  \bmhead{Competing interests} The author has no competing interests to declare that are relevant to the content of this article.
  \bmhead{Data availability} No datasets were generated or analysed during the current study. [If code or computations support any claim, give a repository link here instead.]
  \bmhead{Author contributions} [single author: sole author] / [CRediT list]
  \bmhead{Use of AI tools} [if applicable; see Section 9]
  ```

## 9. AI and large language models
Journal guidelines [G, Title Page]:
> "Large Language Models (LLMs), such as ChatGPT, do not currently satisfy our authorship criteria. Notably an attribution of authorship carries with it accountability for the work, which cannot be effectively applied to LLMs. Use of an LLM should be properly documented in the Methods section (and if a Methods section is not available, in a suitable alternative part) of the manuscript. The use of an LLM (or other AI-tool) for "AI assisted copy editing" purposes does not need to be declared. In this context, we define the term "AI assisted copy editing" as AI-assisted improvements to human-generated texts for readability and style, and to ensure that the texts are free of errors in grammar, spelling, punctuation and tone. These AI-assisted improvements may include wording and formatting changes to the texts, but do not include generative editorial work and autonomous content creation. In all cases, there must be human accountability for the final version of the text and agreement from the authors that the edits reflect their original work."

The current publisher-wide framework [P] uses three risk levels:
- **Green (permitted):** "Using an LLM to polish or refine the language", "Stress-testing research questions", and similar assistive uses. "Disclosure enhances trust".
- **Amber (permitted with oversight and disclosure):** "Suggesting analytical, experimental or methodological approaches", "Drafting explanatory summaries", "Comparing results to existing literature", "Extensive copy editing or writing support". "Permitted with human oversight, verification, and transparency through disclosure."
- **Red (not permitted):** "Generating hypotheses, analyses or conclusions and presenting them as human-derived", "Fabricating data, citations or results", "Using an LLM to generate core research reasoning without disclosure", "Assigning authorship or accountability to AI systems or tools", "Creating photorealistic images (deepfakes)".
- Authors: "Disclose AI use for trust and transparency".

Citations [P]: "non-existent/hallucinated references generated by an artificial intelligence (AI) tool" count as unethical. Authors must "Carefully review citations following any use of AI in manuscript preparation".

AI images: [G] says "Please check Springer's policy on generative AI images". The older stand-alone policy said Springer Nature is "unable to permit" generative-AI images, with narrow exceptions. That text no longer appears on the current [P] page; only the deepfake prohibition remains. Practical rule: include no AI-generated figures.

Applying this to Paper D: a pure-math paper has no Methods section. If AI went beyond copy editing (for example proof search, computation, drafting, or Lean or code assistance), disclose it in a short section or paragraph, either an "Acknowledgements"-adjacent note or an item under Declarations. Describe what was done and state that the authors verified everything. No AI tool may appear as an author.

## 10. Preprints and arXiv [P]
> "Springer Nature journals encourage posting of preprints of primary research manuscripts on preprint servers of the authors' choice ... preprints may be posted at any time during the peer review process. Posting of preprints is not considered prior publication and will not jeopardize consideration at Springer Nature journals."

> "Authors should disclose details of preprint posting, including DOI and licensing terms, upon submission of the manuscript ... Once the preprint is published, it is the author's responsibility to ensure that the preprint record is updated with a publication reference, including the DOI and a URL link to the published version".

Any license is allowed for the preprint.

## 11. References [G]
- > "Reference citations in the text should be identified by numbers in square brackets." Entries are "numbered consecutively". The list should contain only works cited and "published or accepted for publication. Personal communications and unpublished works should only be mentioned in the text."
- "If available, please always include DOIs as full DOI links".
- Journal names use ISSN LTWA abbreviations. Example: "Hamburger, C.: Quasimonotonicity, regularity and duality for nonlinear systems of partial differential equations. Ann. Mat. Pura Appl. 169, 321–354 (1995)". In sn-jnl this is the `sn-mathphys-num` option.
- arXiv preprints can be cited per [P]: "Preprint at http://arxiv.org/abs/..." Note the tension with [G] on unpublished works. arXiv citations are common in JOTP in practice.

## 12. Cover letter
No dedicated cover-letter requirement. The corresponding author is responsible for "providing transparency on re-use of material and mention any unpublished material (for example manuscripts in press) included in the manuscript in a cover letter to the Editor" [G]. Suggested-reviewer identity information may go "in the submission letter" [G]. Use the cover letter for: a statement that the paper is original and not under review elsewhere; the arXiv ID and license; related or companion papers (Papers A–C) and how D differs (to avoid salami-slicing concerns: "A single study should not be split up into several parts" [G]); and the AI disclosure summary.

## 13. Suggested and opposed reviewers
- [G]: "Authors are welcome to suggest suitable reviewers and/or request the exclusion of certain individuals ... make sure they are totally independent and not connected to the work in any way. It is strongly recommended to suggest a mix of reviewers from different countries and different institutions. ... the Corresponding Author must provide an institutional email address for each suggested reviewer ..."
- [P]: exclusions are "usually a maximum of two people/research groups". "Authors should not recommend recent collaborators or colleagues who work in the same institution". Required details are "institutional email address and ORCID or Scopus ID". "Each manuscript should be reviewed by at least one reviewer who was not suggested by the author."

## 14. Review model [E]
> "Research content published in this journal is peer reviewed (single-anonymous)."

Author names stay on the manuscript, so no anonymization is needed. Springer usually uses "at least two independent, expert peer reviewers" [P].

## 15. Timelines
- Journal metric [H]: "Submission to first decision (median) 7 days". This mostly reflects desk decisions.
- My own sample of 39 JOTP articles (DOIs s10959-024-01393 to s10959-025-01433, published Dec 2024–Jul 2025), using the publication histories on their article pages:
  - Received to accepted: median **276 days (~9 months)**, IQR 194–416 days, range 63–1077.
  - Received to "Revised": median ~217 days (~7 months).
  - Accepted to online: about 3–5 weeks.
- A 2026 example (s10959-026-01532-2): received 2025-08-07, revised 2025-12-15, accepted 2026-05-05 (~9 months).
- Impact Factor 0.7 (2025); 5-year IF 0.9 [H].

## 16. Other
- Figures: EPS for vector art (PDF via pdflatex works in practice), at least 0.3 pt lines, Helvetica/Arial lettering, captions starting with bold "Fig. n" and no trailing punctuation [G].
- Plagiarism screening may be used; COPE member [E].
- "Changes of authorship ... are not accepted after acceptance" [G].
- Data/code: "authors must add a Data Availability Statement to original research articles"; repositories strongly encouraged [G]. Any computational evidence for Paper D should be deposited, for example on Zenodo or GitHub with a DOI, and cited with a DataCite-style reference.
