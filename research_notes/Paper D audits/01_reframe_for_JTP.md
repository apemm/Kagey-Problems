# Paper D, reframing for the Journal of Theoretical Probability

October 24, 2026. Folder `kagey-problems/problem131/paperD`, with the coverage files in
`kagey-problems/problem131/lean/PaperD`.

## Title

New title: "The elephant random walk with rare reversals: a Luria–Delbrück approximation and the
shape of the law".

Alternatives.

1. "Rare reversals in the elephant random walk: compound Poisson approximation, Landau local limit
   and two humps"
2. "The elephant random walk with vanishing reversal probability: a Luria–Delbrück approximation and
   its consequences for modes and crossings"

## Abstract (journal version)

In the elephant random walk each step copies a uniformly chosen earlier step and reverses it with
probability ε. We study the regime in which ε tends to 0 as the number of steps N grows, with Nε of
order log N. Let M_N be the number of steps that disagree with the first step. We prove an explicit
total variation bound between the law of M_N and a truncated Luria–Delbrück law, the compound Poisson
law with jumps d at rates Nε/(d(d+1)). A local limit theorem with an explicit rate follows, with the
Landau density as the limit. The same Landau law arises from the fixed-memory superdiffusive limit as
the memory tends to 1. We then derive the shape of the law of the position. Every mode lies near one
of the two ends, at a distance x log x + λ_L x + O(√(x log x)), where x = Nε and λ_L ≈ −0.2228 is the
mode of the Landau density. The second difference of the law changes sign at most 4 times. For even N
the probabilities of the origin and of each end cross exactly once, at
Nε = 2 log N − log log N − log 16 + o(1). At the crossing, for every even N ≥ 8, the origin is the
unique interior minimum and the law has exactly 2 symmetric intervals of modes. This last result uses
certified computations at finitely many lengths.

Length about 230 words (pdftotext counts 237 tokens, including split math). The previous sentence on
the relative error of 4ε/(N+2) was cut to stay under 250. That bound is still Theorem 1.3(b).

## What changed

1. Reframing. The introduction opens with the regime. Its second paragraph states the total
   variation approximation and the Landau local limit as the main result and calls the modes, the
   shape and the crossing consequences. The main results are now Theorem 1.1 (the approximation,
   total variation plus local limit, label `thm:main-bulk`), Theorem 1.2 (the modes, new label
   `thm:main-modes`), Theorem 1.3 (the center and the crossing, `thm:main-center`), Theorem 1.4 (the
   shape, `thm:main-shape`) and Proposition 1.5 (`prop:main-window`). The body sections keep their
   order and numbering. Problem 131 is named once, in the acknowledgments. The old third paragraph
   (Kagey's question and the Galton-board name "bins") is gone. "Bin" is replaced by "value",
   "point" or "steps from the end" in the text, the caption, `figures/captions.md`, the axis label
   of Figure 2 (redrawn from cached data), the S sections, the README and the printed labels of
   `verify_elephant_odd.py` and `verify_elephant_shape.py`. "Rows" of certificates in Section 5 are
   now "entries". The paper is not described as part of a series anywhere.
2. Online Resource dropped. `problem131_memory.tex` no longer loads `xr-hyper`. Every pointer to
   Online Resource 1 or an S number goes through a new macro `\arxivonly{Theorem}{label}`. In the
   journal build it prints "the arXiv version of this paper [35]", where item `arxivD` reads
   "arXiv number to be added" with the comment `% arXiv id in November`. In the arXiv build it prints
   the S number and the item is left out. Pointers replaced: intro (S1.7, organization), Section 2
   end (S1.1, S1.2, S1.7), Figure 2 caption and Section 3.4 (S2.1), odd N (S3.1), Appendix B (S2.1).
   The likelihood theorem is gone from the journal paper (intro sentence, end of Section 4,
   Section 5). Hoeffding (1963), cited only in S1, moved to `online_resource_bib.tex`. Data
   availability now says there is no supplementary material and names the arXiv version.
   `online_resource.tex` and `online_resource.pdf` were deleted (recoverable from git).
   `problem131_arxiv.tex` still appends S1 to S4, now under the heading "Further results".
3. Citations, both verified against primary sources.
   - X. Fan and Y. Qi, "A generalized elephant random walk with time-dependent memory",
     arXiv:2610.16065 (v1, 12 October 2026, math.PR). Checked on the arXiv abstract page and in the
     PDF. The model replaces the memory parameter p by a sequence p_n.
   - R. Roy, M. Takei and H. Tanemura, "The elephant random walk in the triangular array setting",
     J. Appl. Probab. 62(3) (2025), 997–1009, doi:10.1017/jpr.2024.106. Checked on Crossref (print
     September 2025, online 16 January 2025) and on arXiv:2403.02881, whose journal reference agrees.
     The PDF defines the walk in row n with a memory window m_n.
   The prior-work sentence now reads "Fan and Qi [11] let the memory parameter of the elephant walk
   vary with time. We vary the reversal probability with the final length, not with time within one
   walk. So our walks form a triangular array, as do those of Roy, Takei and Tanemura [12], whose
   memory window varies with n."
4. Convexity window demoted. Old Theorem 1.3(c) is removed. Proposition 1.5 states the eventual
   window with an uncomputed threshold N_1, the certified range 5 ≤ N ≤ 2000 at the crossing, and
   Conjecture 3.26 for N > 2000. `thm:convex-large` is now Proposition 3.23. The intro of
   Section 3.6, Remark 3.27, the S3 proof and the coverage table were updated to match.
5. Code availability macro. Skipped at the author's request. The statement and its URL are as they
   were.
6. The abstract is within 150 to 250 words.

The note on the use of AI is unchanged. Its reference to Section 5 still resolves. It still mentions
"the Online Resource", as the author's own text. The author may want to update that phrase.

## Builds and checks

- `problem131_memory.tex`: 40 pages (39 before). Three runs, no undefined references, no multiply
  defined labels, no overfull boxes.
- `problem131_arxiv.tex`: 53 pages. Three runs, same result. One run in the middle failed to read
  its .aux, most likely because OneDrive locked it. Two more runs were clean.
- `py -B verify_all.py --quick`: all 4 scripts passed in 3.1 min. The output is in
  `data/verify_output_2026-10-24.txt`.
- Auxiliary files deleted. The PDFs are kept.

## For the author

- Hashes. Changing the printed labels of `verify_elephant_shape.py` breaks the link to the sha256
  recorded in the header of `data/witnesses_convex_2026-10-17.jsonl`. The README now says the
  witnesses match the file at the pinned commit `6f7f9068` and gives the new hashes. The paper's code
  pin is still `6f7f9068`, so the scripts it cites print "bin". A new checked commit would be needed
  to move the pin.
- `../SUPPLEMENT.md` (outside the allowed folders) still describes the Online Resource.
- The repository URL and the folder path `kagey-problems/problem131` in Data and Code availability
  still contain the word Kagey, because item 5 was skipped.
- `lean/PaperD/MAP.md` has new rows for 1.1 to 1.5 and a new header. Its body still uses the
  October 23 numbers and keeps Lean identifiers such as `ewBin`.
