# Problem 001: rectangle identifiability

Black out as many points of an n x m grid as possible so that every rectangle with corners on grid
points (tilted ones included) is still determined by its visible corners. The blackout is chosen
before the rectangle.

## Results

These are proved in the paper `jis/pemmasani.tex`. Results marked (computer) rest on a finite
computation, checked by at least two separately written programs. f(h,m) is the maximum blackout of
h rows and m columns, and a_h(m) is the number of maximum blackouts.

- Every grid: h+m-1 <= f(h,m), and f(h,m) <= m + floor(h^2/4) for m >= 3.
- Two rows, m >= 3: f = m+1, with exactly m*2^(m-1) optima (Strip Theorem).
- Three rows, m >= 3: f = m+2. The optima are counted exactly:
  a_3(m) = 4(m-1)(3m+2)3^(m-5) + E_m for m >= 4, with a closed form for E_m, a rational generating
  function, and a_3(m) ~ (4/81) m^2 3^m.
- Four rows: f = m+4 for m >= 6, and f(4,4) = 7, f(4,5) = 8 (computer). No valid blackout hides a
  rectangle for m >= 4. The generating function of a_4(m) is rational with a denominator of degree
  420, and a_4(m) ~ c m^4 3.3520^m (computer).
- Five rows: f(5,5) = 10, f(5,6) = 11, f(5,7) = 12, and f(5,m) = m+6 for every m >= 8 (computer,
  with the finite collar theorem).
- Six rows: f(6,m) = m+9 for every m >= 15, and f(6,m) <= m+8 for 8 <= m <= 14 (computer).
- Small cells (computer): f(6,6) = 12, f(6,7) = 13, f(7,7) = 14, f(6,8) = 15, f(7,8) = 16. The guess
  f = h+m for both sides at least 4 fails at 5 x 8 and 6 x 8.
- Square grids: f(n,n) >= c n^(6/5) (1+ln n)^(-2/5) for some c > 0 and all large n.
- A tilted lattice rectangle of height n has width at most floor(n^2/4) + 1 = A033638(n), with
  equality possible. This proves the conjecture in A338885 that its row n has largest entry
  A033638(n).

The key step is that the axis-aligned rectangles are identifiable exactly when the row-column
incidence graph of the blackout has no 4-cycle and no 6-cycle (m >= 3). Replacing each column by a
tree on its black rows gives a triangle-free graph on the rows, and Mantel's theorem gives the
upper bound. The constructions for three and four rows are checked against every tilted rectangle.

The main write-up is `notes/notes.pdf` (source `notes/notes.tex`): detailed notes that walk
through every result with small examples and about 25 figures. The figures are drawn by
`notes/make_figures.py`, which checks every blackout it draws against the definition first. The
paper is `jis/pemmasani.tex` (sections in `jis/sections`, compiled: `jis/pemmasani.pdf`), and
`jis/pemmasani_jis.tex` is the same paper as one file, built by `jis/scripts/make_jis_single_file.py`.

## Verification

`python verify_narrow.py` (standard library only) enumerates rectangles by their diagonals, checks
the incidence-graph lemma on 74,304 blackouts, checks the tilted rectangle lists and the
constructions at widths up to 128, and runs the two finite four-row checks.

The ILP engine and the brute-force oracle used for the table of values are in `solver/`, with
their tests; they need the packages in `requirements.txt`. The predictions and their outcomes are
in `data/ledger.md`. Section 9 of the paper proves that the SAT encodings behind the
computer-assisted bounds are faithful and lists, for each computer-assisted statement, its method,
its independent check and its evidence file; `jis/scripts/README.md` gives the commands.

Build the notes from `notes/` with `python make_figures.py` and then `pdflatex notes.tex` (3
times). Build the paper from `jis/` with `pdflatex pemmasani.tex` (three times).

`game/index.html` is a playable version of the problem on grids up to 10 x 10 (open it in a
browser). It is the rectangle game from my website, with larger grids.

## Open

- Classify and count the optima for three and four rows.
- Excess-1: blackout n+m when both dimensions are at least 5.
- Compare the incidence-cycle formulation with the test-cover and extremal graph literature.
