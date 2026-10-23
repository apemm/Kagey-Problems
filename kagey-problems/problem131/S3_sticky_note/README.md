# S3: sticky priors and the most likely count vector

A working note on sticky priors for hidden Markov models. It was Section 6 and Appendix D of
Paper C until October 2026, when Paper B was merged into Paper C and the application to sticky
priors moved out. The mathematics is unchanged.

Given the kernel Pi of the switches and a common exit probability h = tau log N / N, the note
finds which states the most likely count vector of the hidden chain uses (Corollary 2.1),
the thresholds tau_- and tau_+ between one state, a proper set and all states
(Proposition 2.2), the fact that among symmetric kernels only the uniform kernel jumps from one
state straight to all of them (Corollary 2.3), the probability of such a direct jump under the
sticky HDP prior with 3 states, about 3 sqrt 3/(8 pi omega) for large omega (Proposition 2.4,
proved in Appendix A), an exact link to the two-state walk (Corollary 2.5) and the masses of the
faces (Proposition 2.6), with the gap between the conditional mode and where the law puts its mass
(Remark 2.7 and Table 1). The mixture over h under the prior is not treated.

## Files

- `s3_note.tex` is the note. It includes `s3_body.tex` (Section 2, the old Section 6 of Paper C)
  and `s3_appendix.tex` (Appendix A, the old Appendix D).
- The note quotes Theorems 3.3 and 4.8, Proposition 5.1, Corollary 5.2 and Example 2.5 of the
  merged Paper C (`../paperC/problem131_switching.tex`). Their numbers are read with the package
  `xr` from `../paperC/problem131_switching.aux`, so build the paper first.
- The checks are the part on sticky priors of `../paperC/verify_sticky_fisher.py`, which stays in
  `../paperC` because it also holds the checks of the note `../S1_endpoint_information_note` and
  the polynomial S_N that `../paperE/verify_planar.py` imports. Its check labels use the numbers
  of this note ("S3, Proposition 2.2" and so on). `../paperC/verify_all.py` runs it.
- The finite steps are in Lean in `../lean/PaperC/Sticky.lean`. The table "Section 7, sticky
  priors" of `../lean/PaperC/MAP.md` lists them with the numbers of this note.

## How to build

Build `../paperC/problem131_switching.tex` first, then run `pdflatex s3_note.tex` in this folder
3 times.
