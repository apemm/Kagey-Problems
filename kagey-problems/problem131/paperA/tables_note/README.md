# The numerator tables (for a later combinatorics note)

These files are the part of Paper A about the numerator tables of Problem 131, taken out of the
paper before it was posted. They are kept here for a later note.

- `app_tables.tex` was Appendix C of Paper A. It has the generating function of the numerators
  (Proposition C.1), the rook paths for p = 2/3 (Theorem C.2, OEIS A035002) and Mathar's blocked
  walks for p = 1/3 (Theorem C.3, OEIS A348595).
- `figures/lattice.pdf` and `figures/lattice.png` were Figure 6 of Paper A, the two bijections.
  They are made by `paperA/figures/make_figures.py`.

The file does not build on its own. It cites Paper A by its labels. Paper A keeps, as Remark 2.3,
the definition of the numerators and the fact that they are weighted word counts. The Lean proofs
of the two bijections are in `lean/PaperA/Tables.lean`.
