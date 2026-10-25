# Problem 131, Paper G: a local Lamperti law

Title: "A local Lamperti law for the occupation count of a lattice Lévy walk with infinite-mean runs".
Target journal: Electronic Journal of Probability (class `ejpecp`, in TeX Live).

## Abstract

A lattice Lévy walk moves in runs of alternating direction whose independent lengths have regularly
varying tails of index alpha in (0,1). Let A_N be the number of right steps among the first N.
Lamperti's theorem gives the limit law of A_N/N. We prove its local form. The rescaled point
probabilities N P(A_N = k) converge to Lamperti's density at one interior point if and only if they
converge uniformly on compact sets, and this happens if and only if both run laws satisfy the strong
renewal theorem. By the characterization of Caravenna and Doney, the local law holds with no further
condition when alpha > 1/2, and for alpha <= 1/2 exactly under their condition for each run law. For
equal tails the density is U-shaped if cos(pi alpha/2) >= alpha and W-shaped otherwise, with exactly
1 or 3 critical points (threshold 0.5946...). Near the ends the law is the tail of a run times a
renewal mass function, and under Doney's local condition this layer matches the bulk uniformly, so the
global mode is at bounded distance from an end for every alpha. For an arbitrary initial run we give
the exact defect in the bulk, a necessary condition, a sufficient condition and an exact criterion,
and a lower bound on the number of local extrema.

## Status

Draft of October 25, 2026, written from `research_notes/Paper G infinite mean/01_report.md` and
restricted to what the audit `02_audit.md` confirms. 27 pages. Builds clean (no undefined or multiply
defined references, no overfull boxes). The one remaining warning, `pagebackref`, comes from the class.

- Theorem A (`thm:local`): one point, uniform on compacts and (SRT) for both laws are equivalent.
  Proposition `prop:lambda` identifies the limit with Lamperti's density. Corollary `cor:local-cases`
  (alpha > 1/2 free, alpha <= 1/2 iff Caravenna-Doney). Corollary `cor:lower` (the lower half of the
  local law under (RV) alone).
- Theorem B (`thm:shape`): U iff cos(pi alpha/2) >= alpha, else W, b = 1. Proposition `prop:pitchfork`
  (the minima near the threshold). Remark `rem:unequal` (b != 1, numerics only).
- Theorem C (`thm:ends`): (a) under (RV). Parts (b), (c) and Corollary `cor:mode` under Doney's (LB).
  Remark `rem:M0` names the missing bound for (b) without (LB).
- Theorem D (`thm:initial`): (a) to (f). The aging-type start is Conjecture `rem:aging`, with the missing
  near-diagonal bound named.
- Theorem `thm:signs`: lower bound on the sign changes, with the end value at j = 0 defined as
  lim Q(N)/T(N). Conjecture `conj:count` for equality.
- No disclosure statement. A comment in the main file leaves it to the author.

## Files

- `problem131_lamperti.tex`, the main file, with `sec_intro`, `sec_setting` (2), `sec_tools` (3),
  `sec_local` (4), `sec_shape` (5), `sec_ends` (6), `sec_initial` (7), `sec_signs` (8),
  `sec_verify` (9), `sec_appendix` (A) and the bibliography `references.tex`. PDF:
  `problem131_lamperti.pdf`.
- `figures/make_shape_figure.py` writes `figures/shape.pdf` and `.png` (Figure 1) in the shared style
  `../figures/series_style.py`.
- `lamperti_law.py`, shared functions (exact law by `eq:run-sum`, Lamperti density, sign changes,
  brute force over sign strings, output header).
- `verify_identities.py`, the identities of Section 2 against all sign strings, N <= 12.
- `verify_shape.py`, the threshold, the critical-point counts, `prop:pitchfork`, the transform
  `eq:stieltjes` in 30-digit arithmetic, and the double integral at alpha = 1/2.
- `verify_local.py`, the exact law at N = 1000, 2000, 4000: Table 1 (`tab:ratios`), the ratios
  1.0149, 1.0105, 1.0075 at alpha = 1/2, the sign-change counts and positions, Table 2 (`tab:ends`),
  the uniform layer, the asymmetric case.
- `verify_initial.py`, the initial-run numbers of Section 9.
- `verify_all.py`, runs the four verify scripts. Every output in `data/` starts with the sha256 of the
  script that wrote it and the date.

## Build and check

    pdflatex problem131_lamperti.tex     (three times)
    py -I verify_all.py                  (about 45 seconds)
    py -I figures/make_shape_figure.py   (redraws Figure 1)

Needs numpy, scipy and mpmath (and matplotlib for the figure). Recorded with Python 3.14.3, numpy
2.4.2, scipy 1.17.1, mpmath 1.3.0, matplotlib 3.10.8.

## For the author to check

1. Lamperti (1958) was not read in the original. The paper only says he proved an occupation time
   theorem for a class of processes and that the density carries his name (as in Margolin-Barkai
   Eq. (7) and Zaburdaev-Denisov-Klafter Eq. (83)). Check what exactly his theorem covers before
   saying more, in particular whether the two-law alternating case is in it (Remark `rem:global`).
2. Mitov-Yanev (2001) is described from the Crossref metadata and abstract only. Check whether they
   have anything local or anything on the end behaviour.
3. Margolin-Barkai: the value 0.5946... is stated in Section III of arXiv cond-mat/0504454 without a
   derivation. Check the journal version (J. Stat. Phys. 122 (2006) 137-167) for a derivation or a
   closed form before claiming the closed form is new.
4. Wang-Schulz-Deng-Barkai: the atom with a boundary layer for 0 < alpha < 1 (Section VII.A) and the
   quotation from Section VIII are taken from the reading in Paper F. Check the page and section.
5. Godrèche-Luck: "give the transform of the occupation time and its limit laws". Check the second half.
6. Citation details not copied from Paper F: Garsia-Lamperti (Comment. Math. Helv. 37), Erickson
   (Trans. AMS 151), Williamson (Pacific J. Math. 25), Doney 1997 (PTRF 107), Mitov-Yanev (AAP 33),
   Starreveld-Bekker-Mandjes (JAP 55), Margolin-Barkai (JSP 122). Add MR numbers.
7. Lemma `lem:cd`: the theorem numbers cited (Ibragimov-Linnik Thm 4.2.1 for Gnedenko's lattice local
   limit theorem, Caravenna-Doney Thm 1.1 Eq. (1.6), Thm 1.4, Section 4.1 Eq. (4.1), Eq. (1.15),
   Berger Thm 2.4) and Feller II Section XVII.6 for the tail of the stable density.
8. Results added in the draft beyond the audited report, each a short consequence of audited steps:
   Corollary `cor:lower`, Proposition `prop:pitchfork`, the local law for the position W_N and its
   match with ZDK Eq. (61), and Appendix A. Check them.
9. Whether to keep Conjecture `rem:aging` (label kept from the report's part (g)) or drop it.
10. Page count 27 against the target of 28 to 32.
