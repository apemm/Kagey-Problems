# Problem 001: rectangle identifiability

Black out grid points so every rectangle is uniquely determined by its visible corners.
Tilted rectangles count; the blackout is chosen before the rectangle.

## Proved values

For m columns:

- Two rows, m>=3: maximum blackout m+1, with exactly m*2^(m-1) optima.
- Three rows, m>=3: maximum blackout m+2.
- Four rows, m>=6: maximum blackout m+4.
- Four rows, m=4,5: maximum blackout m+3. These finite boundary cases are
  computer-assisted, checking all 72 and 1,440 possible upper-bound equality cases.

The new structural result is that axis-aligned identification is equivalent to absence
of 4- and 6-cycles in the black row-column incidence graph (m>=3). Replacing each column
neighborhood by a tree yields a triangle-free graph on row vertices. Mantel's bound gives
the general upper bound m+floor(n^2/4). Explicit constructions attain the narrow-row
bounds, with a complete tilted-rectangle analysis.

The general-width proofs are in [paper/narrow_rows.tex](paper/narrow_rows.tex), included
in [paper/main.tex](paper/main.tex). The compiled paper is `paper/main.pdf`.

## Verification

Run `python verify_narrow.py` (standard library only). It independently enumerates
rectangles by their diagonals, checks the incidence characterization on 74,304 blackouts,
verifies tilted shape lists and constructions at selected widths through 128, and
exhaustively settles the two finite boundary exclusions.

Original ILP and brute implementations remain in `solver/`, with their existing tests.
The original computational claims have different verification levels, recorded in the
paper's table. The new verifier does not require the ILP dependencies.

Build from `paper/` by running `pdflatex -interaction=nonstopmode -halt-on-error main.tex`
twice. The original prediction history is preserved in `data/ledger.md`.

## Remaining targets

- Classify/count three- and four-row extremizers.
- Resolve the higher-dimensional Excess-1 conjecture, where both dimensions are >=5.
- Compare the incidence-cycle formulation with test-cover and extremal graph literature.
- For an eventual probability direction, formulate random erasures/noisy observations
  explicitly; no probabilistic threshold theorem is claimed here.
