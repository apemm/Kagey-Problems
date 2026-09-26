# Problem 131: earlier work

Notes on what each source proves, so the papers only claim what is not already there.

## Same model

**Renshaw and Henderson (1981)**, *The correlated random walk*, J. Appl. Probab. 18, 403-414
([JSTOR](https://www.jstor.org/stable/3213286)). Same walk, with continuation probability p, an
unbiased first step, and a Galton-style pinball machine as motivation. Eq. (2.1) is the run-count law and
(2.6)-(2.8) are the generating function and the even/odd formulas. Page 408 discusses the upturn
at the endpoints and Section 3 the diffusion limit. Section 4 fixes p^n = exp(-mu) as n grows, gets
an interior Bessel limit in Eq. (4.4) with a unique interior maximum (p. 412), and then expands that
limit as mu grows in Eq. (4.6). These are two limits taken in turn. There is no error bound at
finite N when mu grows like log N, and no crossing theorem, which is what Paper A adds.

**Dekking and Kong (2011)**, *Multimodality of the Markov binomial distribution*
([arXiv:1102.3613](https://arxiv.org/abs/1102.3613)). They assume 0 < a, b < 1 and an arbitrary
initial distribution, with no stationarity. Proposition 4.3 (p. 12) is log-concavity of
f_n(1), ..., f_n(n-1), and the paragraph after it gives the strict version for j = 2, ..., n-2. The
condition a + b >= 1 belongs to Proposition 4.2 (the sequence with endpoints), not 4.3. Our model is
a = b = 1-p with initial law (1/2, 1/2), so their result covers 0 < p < 1 and gives the ordering of
the interior bins. It does not say where the center crosses the endpoints. Paper A proves the
ordering again from the coefficients since that proof also gives the strict gap it needs.

**Herrmann and Vallois (2010)**, *From persistent random walk to the telegraph noise*
([arXiv:0810.0650](https://arxiv.org/abs/0810.0650)). Telegraph limit, Bessel density and the atoms
from walks with no switch.

**Cekanavicius and Mikalauskas (2001)**, *Local theorems for the Markov binomial distribution*,
Lithuanian Math. J. 41, 219-231 ([doi](https://doi.org/10.1023/A:1012802428342)). Theorem 1.1
(p. 220) assumes p, qbar <= 1/2, with p the persistence in state one. Their *Large deviations for the
Markov binomial distribution*, same volume, 307-318 ([doi](https://doi.org/10.1023/A:1013840819221)):
Theorems 1.1-1.2 (pp. 308-309) need p <= 1/50 and Theorem 1.3 needs p <= qbar. Neither covers the
symmetric window p -> 1 used here. The later local-law notes list the first paper as "not read" in
their own search, which did not reopen it because Paper A already cited it. The theorem numbers and
pages above come from the earlier reading. Recheck both papers against these lines before submission.

**Goldstein (1951)**, *On diffusion by discontinuous movements, and on the telegraph equation*,
Quart. J. Mech. Appl. Math. 4, 129-156
([OUP](https://academic.oup.com/qjmam/article-abstract/4/2/129/1874849)). Abstract read on
2026-09-26, not the paper. Particles move in steps of time tau, half start in each direction, and each
new step keeps the direction with probability p and reverses it with probability q = 1-p. He finds the
difference equation, asymptotic formulas for large n at fixed p/q and at fixed nq/p, and the telegraph
equation in the limit. So this is the same walk, and Paper A cites it only for the origin of the model.

**Gillis (1955)**, *Correlated random walk*, Proc. Cambridge Philos. Soc. 51, 639-651. Abstract read,
not the paper. A walk on the d-dimensional lattice whose step law depends on the previous step. Paper
A cites it only for the origin of the model.

**Wald and Wolfowitz (1940)**, *On a test whether two samples are from the same population*. Not
checked (the paper is behind a paywall and no statement was read), so Paper A no longer cites it. The
run-count law is taken from Renshaw and Henderson, Eq. (2.1), and proved in Paper A.

## Ising chain

**Antal, Droz and Racz (2004)** ([arXiv](https://arxiv.org/abs/cond-mat/0308442)). Free and periodic
magnetization distributions at fixed scale, with Bessel densities and the boundary atoms.

**Dantchev and Rudnick (2022)** ([arXiv:2207.01134](https://arxiv.org/abs/2207.01134)). Exact free
and periodic coefficients, including the cyclic run polynomial used in Paper A, and the Bessel scaling.

**Stepanyan, Tzortzakakis, Petrosyan and Allahverdyan (2024)**
([arXiv:2307.15479](https://arxiv.org/abs/2307.15479)). Periodic chain,
H = -J sum s_j s_{j+1} - h sum s_j, with h = 0 in Section III.B. They find the exact periodic
endpoint/adjacent threshold. For endpoint/center (P(m = +-N) = P(m = 0), so even N) Eq. (16) gives
beta J ~ (2 log N - 1)/5 "to a good approximation", and the caption of Fig. 1(b) gives the fit
beta J ~ 0.3864 log N - 0.21055. Neither comes with an error bound. So the crossing question is
theirs, and Paper A's beta J = (log N - log log N)/2 + ... is a large-N expansion with a proof, not
a correction of a theorem they stated.

## Multistate (Paper B)

**Wang and Yang (1995)**, *On a Markov multinomial distribution*, Mathematical Scientist 20, 40-49.
We could not get a copy. It is cited in **Wang and Tang (2003)**, *Poisson style convergence theorems
for additive processes defined on Markov chains*, Statistica Sinica 13, 227-242
([pdf](https://www3.stat.sinica.edu.tw/statistica/oldpdf/A13n114.pdf)). The finite sum in Paper B
is a special case of this theory and is not claimed as new.

**Brydges, van der Hofstad and Konig (2007)** ([arXiv](https://arxiv.org/abs/math/0611525)).
Occupation densities for continuous-time chains on the visited faces of the simplex. For the
complete-graph generator the rate is I(alpha) = d - (sum sqrt(alpha_i))^2, so the exponent
(sum sqrt(alpha_i))^2 - 1 in Paper B is the difference from the vertex rate and is not new. Their
densities do not give the discrete comparison of one bin with a vertex when p depends on N.

**Stadje (1999)**, *Joint distributions of the numbers of visits for finite-state Markov chains*,
J. Multivariate Anal. 70, 157-176 ([doi](https://doi.org/10.1006/jmva.1999.1814)). Generating
functions for the joint visit counts of a finite chain, and limit laws when one state is nearly
absorbing. Close in spirit to the near-vertex regime, but no crossings or relative errors. Only the
abstract has been read, so the full text should be checked against the near-vertex section of
Paper B.

**Huang, Kious, Sidoravicius and Tarres (2018)** ([arXiv:1803.06930](https://arxiv.org/abs/1803.06930)).
Density of local times of continuous-time chains on finite graphs, with Bessel functions. The
continuous-time analogue of the Bessel representation in Paper B.

**Potts chain.** The model is the 1D d-state Potts chain with free boundaries, with
p = e^K/(e^K+d-1), and the weak-field section of Paper B is the Potts chain in a field of size
h/N. Kassan-Ogly and Filippov (2003), *Exact solutions of one-dimensional Potts models in magnetic
field*, J. Magn. Magn. Mater. 258-259, 219-221, solve the chain in a field in the thermodynamic
limit. A search on 2026-09-24 found no work on the Potts chain at a fixed occupation vector (the d-state
version of the fixed-M ensemble of Dantchev and Rudnick), and nothing on the crossings, the
Laguerre laws or the weak-field face phases.

## OEIS

[A035002](https://oeis.org/A035002) and [A348595](https://oeis.org/A348595) already have the
generating functions of the p = 2/3 and p = 1/3 tables. The bijections in Paper A explain why.

## Summary

Known are the exact law, the normal limit, interior log-concavity, the Bessel scaling at fixed
scale, the periodic law, and the periodic endpoint/center question. Not found in these sources are
the bin-independent relative error bounds, the uniform expansion over all bins with the Laguerre
edge law and the matching between them, the log 2 shift between boundaries, the superlevel-set
window, and the multistate crossing constants and near-vertex results. The balancing argument in
Paper B uses the standard fact that the binomial transform preserves log-concavity.

