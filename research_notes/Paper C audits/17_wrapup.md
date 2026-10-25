# Paper C audit 17. Wrap-up after the split and the revision of Paper F

October 24, 2026. This pass checks the imports of C2 against C1, splits the Lean map, and brings
the top-level README, the top-level runner and the Lean READMEs up to date with Papers C1, C2 and F.

## 1. The imports of C2

`paperC2/sec_prelim.tex` cites 13 C1 numbers. Each was checked against `paperC/EXPORTS.md`, the
text of `paperC/problem131_chains.pdf` (70 pages) and the `.aux` of a fresh build of C1 made
outside the repository. The numbers are Lemma 2.2(b), (c), Theorem 4.2(ii), Lemma 3.2,
Propositions 3.1 and 3.4, Lemma 4.1 with equation (6), equation (1), Theorem 4.2 with Remark 4.3,
Theorem 4.2(iii), Definition 5.1, Proposition 5.2, Theorem 5.7 and Theorem 5.6. The other C2 files
cite Theorem 4.4, Theorem 5.8, Lemma 2.3 and Proposition 5.16, also checked. All agree, the parts
included, and so do the headings of the Springer build. No number drifted, so `sec_prelim.tex` was
not changed and C2 was not rebuilt.

## 2. The Lean map

`lean/PaperC/MAP.md` now has a section for C1 and one for C2, with the numbers of the builds of
October 24. The old tables used the numbers of the EJP version, so every row was renumbered through
its label and the archived PDF. The modules table says which paper each module serves.

- C1. `DVRestriction` (Proposition 3.1, equation (3)), and the older modules for Sections 2 to 5,
  7, 8 and Appendices C and D. The 4-cycle rows now point to Section 4.1, the complete-graph and
  complement rows of the old Table 2 to Remark 7.4, and the old Remark 5.11 to Step 3 of
  Corollary 7.11.
- C2. `PrincipalMinors` (Section 3.1 and step (N) of Theorem 3.5), `GeneratorFiber` (step (N),
  Theorem 3.5(a) and (d), Remark 3.6) and `CriticalWindow` (Example 6.5 with Proposition 6.3).
- A third section keeps the rows whose statements neither paper states. These are the rows `C_d`,
  `P_d`, `Θ_ε`, the paw, the house and `K_4` plus a vertex of the old Table 2, `K_arc3` and
  the identity of the old Corollary 7.1(c), the old Example 5.15 and the star zero set.

Unclear homes. The sign lemma (`sign_constant`) is not a numbered statement of C2. Only Section 7
names it, so the map says that. The old Example 5.15 (`triangle_edge_phase`) is close to Step 4 of
Corollary 7.11 but is not stated there, so it went to the third section. The row `full_beats`
stays with Theorem 4.4, as in the old map, though C1 states the nearest fact after Lemma 3.2.

The docstrings of the 4 new modules and of `PaperC.lean` now name the paper files and the current
numbers. No proof was changed. `lake build PaperC` in the workspace `~/lean-work/paperC`, whose
source folder is the repository's `lean` folder, completed with no errors (8726 jobs).
`lakefile.toml` still calls Paper C `paperC/problem131_switching.tex` in a comment. That file was
outside the write scope.

## 3. README and runner

`kagey-problems/problem131/README.md` now describes C1 (JTP, 70 and 77 pages), C2 (SPA, 40 pages)
and F (EJP, 55 pages, complete), the three archives, the note S4 under its current title, and the
four builds (C1 article and Springer, C2 `elsarticle`, F `ejpecp`). Paper B is now said to be in
C1. `verify_all.py` has the choice `c2`, which runs `paperC2/verify_all.py` with no flag, since
that runner takes none, and keeps `c` for C1 with `--quick` or `--full`. The times are those of the
latest recorded runs (C1 567 s, C2 157 s, F about 20 s). `py -I verify_all.py --dry-run` lists the
expected commands. The full suite was not run.

The Lean README names C1 and C2 and drops the sentence that called Paper F a skeleton. The
top-level `kagey-problems/lean/README.md` does not mention Paper C and was left alone.

## 4. Sweep

Hits in the folders named in the brief, PDFs included through their text.

- `paperC/removed_proofs/full_2026-09-26/problem131_switching.tex`, line 77. The acknowledgment of
  the draft of September 26 on how the Lean code and the writing were produced. It is a paper's
  own note and was left.
- `paperC/data/ledger_C2.md`, lines 3 and 253. Both named a temporary folder for the code of the
  ledger. The wording now names a working folder that is not in the repository.
- `research_notes/C theorems 5 and 7/09_hypL_check_stderr.txt`, line 12. A numpy warning that
  prints the path of the Python installation. Left, since it is recorded output.

No other file matched.
