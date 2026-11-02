import PaperD.RevisionJensen
import PaperD.RevisionWeakChar
import PaperD.Modes.RevisionShape

/-!
# Formalization of the November 2026 manuscript strengthenings

* The exact first-flip weights give the Jensen center bound.
* A direct characteristic-function proof gives the weak Landau limit under
  `x² log² N / N → 0`, without the old Scheffé input.
* The smoothing equation gives a stretched-exponential Fourier bound,
  entire densities, and the derivative regularity needed for strict shape.
* The finite-walk five-sign bound passes to the limiting second derivative.
  The resulting strict curvature partition and exact local-mode sets are proved.
* A direct density comparison gives the unimodal fourth-moment inequality.
  With the cited raw moments this proves bimodality for memory at least `4/5`.

The cited probabilistic limit-law, fixed-point/Fourier, and moment inputs are
explicit hypotheses. They are not new axioms and are not counted as proved
literature results. See the statement-by-statement coverage report.
-/
