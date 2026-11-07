import PaperD.RevisionJensen
import PaperD.RevisionWeakChar
import PaperD.Modes.RevisionShape
import PaperD.Modes.BiasLimitTransfer
import PaperD.Modes.BiasEntire
import PaperD.BiasedModesList
import PaperD.Modes.RevisionNearOne
import PaperD.Modes.TransitionBounds
import PaperD.Modes.TransitionClassification
import PaperD.Modes.TransitionSmoothingIntegral
import PaperD.Modes.TransitionIntegrals
import PaperD.Modes.BiasWeakTransferFinal
import PaperD.Modes.BiasIntervalEndpoint
import PaperD.Modes.EJPBiasDerivativeCutoff
import PaperD.EJPBiasBoundary
import PaperD.EJPModeStability
import PaperD.EJPGlobalModeGap
import PaperD.EJPModeAnalyticRange
import PaperD.EJPBiasUniform
import PaperD.EJPBiasValueBound
import PaperD.EJPRefinementAlgebra
import PaperD.EJPFiniteThreshold
import PaperD.EJPStrictNegativeHalf
import PaperD.EJPStrictSlopeAlgebra
import PaperD.EJPBalancedStart
import PaperD.EJPPositiveStartTwo
import PaperD.EJPFiniteShapeStability
import PaperD.EJPFiniteCentralZero
import PaperD.EJPAnalyticThresholdBounds
import PaperD.EJPAnalyticThresholdOrder
import PaperD.EJPAnalyticThresholdMellin
import PaperD.EJPAnalyticThresholdSeriesEndpoint
import PaperD.EJPAnalyticThresholdParamModel
import PaperD.EJPAnalyticThresholdComparison
import PaperD.EJPAnalyticThresholdFinal
import PaperD.EJPAnalyticThresholdFinalRegularity
import PaperD.EJPModelThreshold
import PaperD.EJPModelFiniteMomentsRRT

/-!
# Formalization of the November 2026 manuscript strengthenings

* The analytic threshold modules construct the H-series, its root and the
  normalized root weights. Singular ODE uniqueness identifies the actual
  exponentially randomized characteristic function. The inverse chart, Mellin
  continuation and final substitution give the central-curvature integral.
  Rational bounds and strict covariance control its parameter dependence.

* The model modules start from the actual finite count laws and ordinary weak
  convergence. Finite even-moment bounds justify passage of all moments to the
  limit. The exact splitting formula gives the distributional fixed point;
  Beta integrals and exponential randomization give the normalized moment
  recurrence and analytic transform equation. The fixed point and nonzero
  mean give full support, initial Fourier decay and stretched-exponential bounds.
  Gaussian approximation and Fourier inversion identify the canonical inverse
  as the density of the actual fair symmetrization.

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
  Fixed lattice-window averages transfer this bound under weak convergence.
* The old weak near-one bridge, together with the proved fair curvature
  partition and published conditional unimodality, gives uniform profiles,
  peak locations and heights, and total variation convergence uniformly in bias.
* The actual finite law has no valley on the half favoured by the initial bias.
  Its weak limit and reflection dominance give a centred open interval of
  bimodal biases, with a unique unimodal maximum outside and at the endpoints.
* The bimodality interval's lower endpoint tends to zero near memory one.
* A positive central-curvature derivative closes a sign bracket into a unique
  modal transition. Negative fourth derivative puts the critical law in the
  unimodal branch. The derivative-tail bootstrap and dominated Fourier
  differentiation are proved with their analytic bounds as explicit inputs.
* The smoothing chain/product derivatives, dominated integral differentiation,
  half-interval reflection, weighted power/log integrals, geometric remainder
  and power-tail integral bounds are now proved separately.
* Portmanteau, the exact atomic-window identity and lattice normalization give
  the centred-interval theorem from ordinary probability-measure convergence.

Existence and ordinary weak convergence of the classical limit law remain
explicit hypotheses. The model-specific threshold assembly derives the moment
and Fourier inputs. Conditional unimodality in the separate bias-interval
theorem remains a cited input. See the statement-by-statement coverage report.
The Arb enclosures, the characteristic-function instantiation of the smoothing
derivatives and the assembly of their uniform tail estimates remain written
and numerical proofs; they are not silently converted into kernel claims.
-/
