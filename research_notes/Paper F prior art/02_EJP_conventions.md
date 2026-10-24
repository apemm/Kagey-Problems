# EJP conventions survey (2026-10-24)

See the final report for full text; this file mirrors it.

## Part 1 (verified sources: Wayback copies of imstat.org pages dated Sep/Oct 2026; ejpecp.cls v1.11.3 and sample.tex, installed in TeX Live 2026)
- Platform: EJMS, https://www.e-publications.org/ims/submission/ ; PDF submitted for review; LaTeX source only after acceptance (to ejournals-ejp@vtex.lt, quote manuscript number).
- Length: no hard EJP cap; "short papers, those less than 12 pages, should be submitted first to ECP". No ECP maximum stated on the pages I could read.
- No fees; CC BY 4.0; board members asked not to submit.
- Class: \documentclass[EJP]{ejpecp} (or ECP). Options: EJP, ECP, NOAMS, NODS, PSTRICKS, draft, final, preprint, nofontexpansion, nobera. pdflatex only (lualatex tested). Loads amsmath, amsthm, amsfonts, amssymb, bera, dsfont, hyperref, geometry (3.5cm margins), graphicx, latexsym, mathtools, microtype. \mathbb is redirected to dsfont (\realmathbb for the original).
- Macros: \TITLE, \SHORTTITLE, \AUTHORS (\and between authors, \footnote{affil. \EMAIL{..}}), \KEYWORDS{a ; b}, \AMSSUBJ{60K05 ; 60G50} (MSC2020), optional \AMSSUBJSECONDARY, \ABSTRACT{..}, \SUBMITTED, \ACCEPTED, optional \ARXIVID, \DEDICATORY, \HALID; editor-set: \VOLUME \YEAR \PAPERNUM \DOI. No \maketitle. Environments: acks ({acks}...{\end acks}), supplement (\stitle, \sdescription). Theorem-like envs predefined: assumption(s), claim, condition, conjecture, corollary, definition(s), example, exercise, fact(s), heuristics, hypothesis/hypotheses, lemma, notation(s), problem, proposition, question, remark, theorem.
- Bibliography: inline thebibliography (not a separate .bib/.bst), numeric labels, sorted alphabetically by author; \MR{} links (use MathSciNet bibtex + amsplain, or BatchMRef); \ARXIV{id} for preprints; arXiv links may stay next to MR links.
- Figures: pdf/eps/jpg/png; \centering, label after caption; the class has no xcolor and sets hyperref link borders off. No stated colour policy found.
- Supplements: {supplement} environment with title+description.
- NOT FOUND: abstract word limit, data/code availability statement, time to first decision. The journal sites (imstat.org, projecteuclid.org) were bot-blocked; only Wayback copies were readable.
