# Problem 001: rectangle identifiability

Black out as many points of an n x m grid as possible so that every rectangle with corners on grid
points (tilted ones included) is still determined by its visible corners. The blackout is chosen
before the rectangle.

## Results

For m columns:

- Two rows, m >= 3: maximum blackout m+1, with exactly m*2^(m-1) optima (Strip Theorem).
- Three rows, m >= 3: maximum blackout m+2.
- Four rows, m >= 6: maximum blackout m+4.
- Four rows, m = 4, 5: maximum blackout m+3, by an exhaustive computer check of all 72 and 1,440
  blackouts that could reach the upper bound.
- Any n, m >= 3: maximum blackout at most m + floor(n^2/4).
- 5 x 5: maximum blackout 10, by hand: the incidence graph has 10 vertices and no 4- or 6-cycle,
  so at most 10 edges. By computer, the optimum is unique up to the 8 symmetries of the square.

The key step is that the axis-aligned rectangles are identifiable exactly when the row-column
incidence graph of the blackout has no 4-cycle and no 6-cycle (m >= 3). Replacing each column by a
tree on its black rows gives a triangle-free graph on the rows, and Mantel's theorem gives the
upper bound. The constructions for three and four rows are checked against every tilted rectangle.

The main write-up is `notes/notes.pdf` (source `notes/notes.tex`): detailed notes that walk
through every result with small examples and about 25 figures. The figures are drawn by
`notes/make_figures.py`, which checks every blackout it draws against the definition first. The
older paper version is `paper/main.tex` (compiled: `paper/main.pdf`).

## Verification

`python verify_narrow.py` (standard library only) enumerates rectangles by their diagonals, checks
the incidence-graph lemma on 74,304 blackouts, checks the tilted rectangle lists and the
constructions at widths up to 128, and runs the two finite four-row checks.

The ILP engine and the brute-force oracle used for the table of values are in `solver/`, with
their tests; they need the packages in `requirements.txt`. The predictions and their outcomes are
in `data/ledger.md`.

Build the notes from `notes/` with `python make_figures.py` and then `pdflatex notes.tex` (3
times). Build the paper from `paper/` with `pdflatex main.tex` (twice).

`game/index.html` is a playable version of the problem on grids up to 10 x 10 (open it in a
browser). It is the rectangle game from my website, with larger grids.

## Open

- Classify and count the optima for three and four rows.
- Excess-1: blackout n+m when both dimensions are at least 5.
- Compare the incidence-cycle formulation with the test-cover and extremal graph literature.
