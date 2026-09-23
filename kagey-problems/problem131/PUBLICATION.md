# Publication and literature notes for Problem 131

Updated September 22, 2026. This is a working assessment, not a novelty certificate.

The strongest candidate contribution is now the uniform endpoint-crossing analysis:
all binary bin distances, fixed-edge Laguerre asymptotics, free/periodic boundary shifts,
the spatial critical window, and multistate simplex-face threshold and mode results.
The follow-up adds a relative Bessel-integral estimate uniform over all positive
compositions, a rare-coordinate crossover at N/log(N)^2, spatial superlevel volumes,
and a weak-field phase diagram that realizes every intermediate support size.
One explicit quadratic field realizes all support sizes consecutively, with proved
ordered transition parameters. These are individual-bin modal transitions, not claims
of thermodynamic phase transitions or probability-mass concentration on a face.
The accompanying manuscript gives analytic proofs and the scripts supply numerical
corroboration. The Lean files verify finite algebraic ingredients, not the analytic limits.

The latest extension completes the leading near-vertex crossing uniformly for every
fixed number of rare colors and arbitrary positive counts with total A=o(b). The
relative root error is O_ell(sqrt((A+1)/b)); unequal rare counts may grow on different
scales. A proved example with two rare counts floor(b/log b) has an unbounded error
in the relative probability approximation while its predicted and exact crossing
roots still agree asymptotically. This separation, and the uniform root theorem,
are stronger publication candidates than the classical mixture representation alone.

The deeper review found **direct prior study of the crossing question**. It would be
incorrect to claim that endpoint-versus-center competition itself is new. The proposed
advance is the quantitative moving-parameter theorem, its explicit constants and its
additional consequences. No exact match to this complete package was found, but priority
remains unconfirmed. A substantial probability/statistical-mechanics note is a more
natural framing than a new exact distribution for a Galton board.

## Direct Ising and occupation-time antecedents

- [Antal, Droz and Racz (2004)](https://arxiv.org/abs/cond-mat/0308442): free and
  periodic magnetization distributions with Bessel densities and boundary atoms.
- [Dantchev and Rudnick (2022)](https://arxiv.org/abs/2207.01134): exact free and
  periodic coefficients, including the cyclic run polynomial used here, and Bessel scaling.
- [Stepanyan et al. (2024)](https://arxiv.org/html/2307.15479v3): the exact periodic
  endpoint/adjacent threshold and a finite-size approximation for endpoint/center equality.
  Our beta J=(log N-log log N)/2+o(1) is a rigorous large-N refinement of that comparison.
  Their finite-size fit should not be misrepresented as a claimed asymptotic theorem.
- [Brydges, van der Hofstad and Koenig (2007)](https://arxiv.org/abs/math/0611525):
  general continuous-time occupation densities on visited-range simplex faces.
  These densities do not by themselves give the discrete moving-scale bin/vertex comparison.
  Their symmetric occupation-rate framework also identifies our square-root exponent:
  for the complete-graph generator, I(alpha)=d-(sum sqrt(alpha_i))^2. The exponent
  (sum sqrt(alpha_i))^2-1 is the rate difference from a vertex, not a new rate function.

The principal apparently additional statements are the bin-independent relative errors,
the uniform all-bin threshold expansion and its Laguerre matching, the log(2) boundary
shift, the critical-window superlevel-set law, and the explicit multistate threshold
constants with an analytic local estimate. The within-face balancing argument is useful
but uses a classical binomial-transform log-concavity mechanism; its standalone novelty
is not claimed. A finite three-direction counterexample prevents an unrestricted
all-N vertex-or-full-center mode claim.

Library access provided the full Cekanavicius--Mikalauskas (2001)
[Local Theorems for the Markov Binomial Distribution](https://doi.org/10.1023/A:1012802428342).
Theorem 1.1 (p. 220) assumes p,qbar <= 1/2, where p is persistence in state one;
the following high-persistence discussion explicitly leaves another range unresolved.
It does not cover our symmetric p -> 1 window. This closes that particular reading gap.
Source-access gaps remain for Renshaw--Henderson (1981) and Wang--Yang (1995).
The additional literature review obtained their separate 2001 paper,
[Large Deviations for the Markov Binomial Distribution](https://doi.org/10.1023/A:1013840819221).
Theorems 1.1--1.2 (pp. 308--309) require persistence p <= 1/50; Theorem 1.3 requires
p <= qbar. These exclude the symmetric p -> 1 regime used here. No equivalent
uniform arbitrary-A=o(b) crossing theorem was found in the inspected sources.
The exact representation uses established binomial/gamma-mixture methods; the
claimed advance is its uniform quantitative root consequence. The manuscript's
introduction and bibliography give the primary-source comparisons and access
qualifications; Section 10 proves the completion theorem.
No matching theorem for the full new package was located. This remains a bounded
literature assessment; the elementary one-factor inequality should not alone be sold
as a frontier discovery. The uniform integrated bound and boundary/mode consequences
give the more substantial research claim.

## Established results and close sources

- [Dekking and Kong (2011)](https://arxiv.org/abs/1102.3613), *Multimodality of the Markov
  binomial distribution*: exact law, variance, interior log-concavity, local modality.
  Their a=b=1-p with symmetric initialization is this model. Their local modality
  classification is distinct from comparing the heights of the center and endpoints.
- [Herrmann and Vallois (2010)](https://arxiv.org/abs/0810.0650), *From persistent random
  walk to the telegraph noise*: classical Bessel density and no-switch atoms.
- [Renshaw and Henderson (1981)](https://www.cambridge.org/core/journals/journal-of-applied-probability/article/abs/correlated-random-walk/34990D29A83426D0BCD80B8C85032DEC):
  the same correlated walk, exact transition probabilities and limiting distributions.
  Only the abstract was obtained.
- Wang and Yang (1995), *On a Markov multinomial distribution*, Mathematical Scientist
  20, 40–49: original not obtained; cited in [Wang and Tang (2003)](https://www3.stat.sinica.edu.tw/statistica/oldpdf/A13n114.pdf),
  *Poisson style convergence theorems for additive processes defined on Markov chains*.
  The d-direction finite sum and CLT are useful specializations, not claimed new laws.
- [A035002](https://oeis.org/A035002) and [A348595](https://oeis.org/A348595) already give
  the relevant generating functions. Kagey points to them; the manuscript's bijections
  explain the connections rather than discovering the sequence identifications.

## Remaining review

Obtain the missing originals and have a subject specialist check the proof and priority.
No journal acceptance or suitability is established by these notes.
