# Problem 131: publication notes

Updated October 2, 2026.

Paper A (`paperA/problem131.tex`, 27 pages) and Paper B (`paperB/problem131_multistate.tex`,
39 pages) are ready for arXiv. Both were revised against the checklists `PaperA_arXiv_edits.md` and
`PaperB_arXiv_edits.md` and refereed line by line.
The repository is tagged `paperA-arxiv-v1` and `paperB-arxiv-v1` at the commit that matches the
posted versions. Paper B proves its start-law results itself (Theorem 4.6, Corollary 4.7,
Example 4.9) and no longer depends on Paper C.

Targets. Paper A goes to the Journal of Applied Probability (at most 30 pages under the Applied
Probability Trust's rule). Paper B, at 39 pages, goes to Advances in Applied Probability or the
Journal of Statistical Physics.

Still to do by hand:
- turn on Zenodo's GitHub integration and create GitHub releases from the two tags to get DOIs,
  then add each DOI to the arXiv comments field and, in a later version, to Section 6 or 7;
- post A first, then B with A's arXiv number in its bibliography;
- strip comments from the sources (`arxiv_latex_cleaner`) and upload only each paper's .tex files
  and `figures/` PDFs (not `llt_note/`, `tables_note/`, `removed_proofs/`, `data/` or scripts);
- read Wang and Yang (1995), The Mathematical Scientist 20, 40-49, through interlibrary loan, and
  Kassan-Ogly and Filippov (2003) in full if possible. Paper B says it has seen only a description
  of the first and the abstract and introduction of the second;
- Renshaw and Henderson (1981) was not rechecked, so Paper A keeps its own short proofs of the
  generating function and the normal limit;
- get an expert read of Theorems 3.3, 3.4 and 4.3 of A and Sections 4 to 6 and Appendix D of B.

Later papers. `paperA/llt_note` is the start of a short paper on the uniform local law (tighten the
constants or settle q > 1/2 first). `paperA/tables_note` could become a Journal of Integer
Sequences note after the Problem 001 paper is decided. Papers C and D are drafts.
