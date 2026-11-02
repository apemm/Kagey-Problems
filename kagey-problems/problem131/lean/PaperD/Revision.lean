import PaperD.RevisionJensen
import PaperD.RevisionWeakChar
import PaperD.Modes.RevisionShape
import PaperD.Modes.BiasLimitTransfer
import PaperD.Modes.BiasEntire
import PaperD.BiasedModesList
import PaperD.Modes.RevisionNearOne
import PaperD.Modes.TransitionBounds
import PaperD.Modes.TransitionClassification
import PaperD.Modes.BiasIntervalEndpoint

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
* First differences of the actual biased finite law exclude two successive
  strict valleys for every nondegenerate memory and every initial bias.
  The named lattice local limit transfers this bound to the analytic density.
* The old weak near-one bridge, together with the proved fair curvature
  partition and published conditional unimodality, gives uniform profiles,
  peak locations and heights, and total variation convergence uniformly in bias.
* The actual finite law has no valley on the half favoured by the initial bias.
  Its local limit and reflection dominance give a centred open interval of
  bimodal biases, with a unique unimodal maximum outside and at the endpoints.
* The bimodality interval's lower endpoint tends to zero near memory one.
* A positive central-curvature derivative closes a sign bracket into a unique
  modal transition. Negative fourth derivative puts the critical law in the
  unimodal branch. The derivative-tail bootstrap and dominated Fourier
  differentiation are proved with their analytic bounds as explicit inputs.

The cited probabilistic limit-law, fixed-point/Fourier, and moment inputs are
explicit hypotheses. They are not new axioms and are not counted as proved
literature results. See the statement-by-statement coverage report.
The Arb enclosures and the detailed differentiated-smoothing integral estimates
remain separate written and numerical proofs; they are not silently converted
into kernel-checked numerical claims.
-/
