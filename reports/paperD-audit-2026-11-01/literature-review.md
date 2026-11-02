# Paper D literature audit

Checked on November 1, 2026. This is a targeted novelty and citation check, not a certification that every related paper has been found.

## Reading record

| Source | Material read in this audit | Outcome |
| --- | --- | --- |
| Pradeep Vishwakarma, *Moments approach for the elephant random walk*, arXiv:2609.11035v1 | Full substantive HTML text, including Sections 1–4 and references; PDF metadata and text also checked | Add as context. Keep the established moment references as proof inputs. |
| Hideki Murahara and Go Tokumitsu, *Optimal Rates in Local and Central Limit Theorems for the Elephant Random Walk*, arXiv:2610.35019v1 | Abstract, introduction, parameter conventions, and local Edgeworth theorem; the 47-page proof was not read in full | Add the regime comparison. |
| Guérin, Laulin, Raschel and Simon, *On the limit law of the superdiffusive elephant random walk* | arXiv full text available; introduction, unimodality proof, Remark 2.1, and analytic-function passages read. Not reread in full | Narrow the conjecture claim. |
| Guérin, Laulin and Raschel, *A fixed-point equation approach for the superdiffusive elephant random walk* | Theorems 1.1–1.4, Section 2.3 and its smoothness argument; not read in full | Provides the fixed-point equation and smoothness, not a cited analytic-density theorem. |
| Trinas and Valle, *A superdiffusive local limit theorem for the elephant random walk and the breakdown of log-concavity* | Abstract and full-text introduction/contents checked; proof not reread | Already positioned appropriately as fixed-memory local-limit and log-concavity work. |

These statements describe this audit's reading, separately from the author's declaration about reading cited sources. “Full text available” does not mean “read in full.”

## New preprints

Murahara and Tokumitsu was submitted on October 26, 2026. Their Theorem 1.1 fixes copying probability `0 <= p <= 3/4` and gives Gaussian local Edgeworth expansions. Paper D takes `p = 1 - epsilon` toward one and obtains a Landau local limit. Their theorem therefore does not subsume Paper D's rare-reversal approximation. The result is useful context, without claiming a sharper rate for the same experiment. [Abstract and metadata](https://arxiv.org/abs/2610.35019), [full text](https://arxiv.org/html/2610.35019v1).

Vishwakarma was submitted on **September 10**, not October. Proposition 2.1 gives characteristic-function and finite-time moment recurrences. Remark 2.7 gives the same first two limiting moments used in Paper D and credits the earlier martingale work. Nothing in its stated results is a modality theorem. There is a gap in the displayed Carleman-bound argument: the sum claimed uniformly at most `1/2` for sufficiently large fixed `K_alpha` contains a positive term proportional to `(m - 2)/K_alpha^2`. That displayed argument cannot establish the claimed bound uniformly in `m`. This audit does not suggest importing it as a proof dependency. [Full text, especially Remark 2.7 and proof of Theorem 2.6](https://arxiv.org/html/2609.11035v1).

Suggested introduction sentences:

```tex
Murahara and Tokumitsu~\cite{muraharatokumitsu2026} obtain optimal Gaussian
local and central limit rates for fixed copying probabilities at most
$3/4$, whereas our local limit concerns copying probability tending to one.
Vishwakarma~\cite{vishwakarma2026} studies moment recurrences and convergence
in the three fixed-memory regimes; our modality argument uses the established
first two moments and the finite-$N$ sign theorem.
```

Suggested bibliography entries:

```tex
\bibitem{muraharatokumitsu2026}
H.~Murahara and G.~Tokumitsu, \emph{Optimal rates in local and central limit
theorems for the elephant random walk}, preprint, 2026.
\href{https://arxiv.org/abs/2610.35019}{arXiv:2610.35019}.

\bibitem{vishwakarma2026}
P.~Vishwakarma, \emph{Moments approach for the elephant random walk},
preprint, 2026.
\href{https://arxiv.org/abs/2609.11035}{arXiv:2609.11035}.
```

## Conjecture and density regularity

GLRS Remark 2.1(b) concerns a threshold in **first-step bias** for each fixed memory, with bimodality near fair initialization and unimodality farther away. It does not state uniqueness of a transition in memory. Paper D's fair-start dichotomy and its certified memory ranges should be described separately; the general bias classification remains outside its scope. The passages about entire or analytic functions concern generating functions, not analyticity of the density. [GLRS full text, Remark 2.1(b)](https://arxiv.org/html/2409.06836).

GLR Theorem 1.3 supplies a positive bounded smooth density. Theorem 2.5 gives Fourier decay faster than every polynomial, with constants depending on the order. That statement alone does not imply analyticity. The fixed-point equation in Theorem 1.1 is the correct starting point for the separate analytic-density lemma developed in this revision. [GLR full text](https://arxiv.org/html/2308.14630).

The proposed lemma was checked independently as follows. For `1 < r < 1/a`, put `D(v) = v^(ar) + (1-v)^(ar) - 1`, positive on `(0,1)`. Choose `K` so that `2 integral exp(-K^r log(2) D(v)) dv < 1`. Riemann–Lebesgue supplies `T` such that the envelope `2 exp(-log(2) (|t|/T)^r)` bounds the characteristic function through `|t| = KT`. At a first crossing beyond this interval, both fixed-point arguments have smaller magnitude, and their product integrates to strictly less than the envelope. Thus no crossing occurs. The resulting decay permits Fourier inversion at every complex argument. This removes flat intervals in the density, but does not prove uniqueness of the memory threshold.

Targeted searches found no further paper settling the fair-start modality transition or proving this exact rare-reversal approximation. This is a search result, not a proof of absence. No new claim of priority for the regularity lemma is recommended without a broader smoothing-transform comparison.
