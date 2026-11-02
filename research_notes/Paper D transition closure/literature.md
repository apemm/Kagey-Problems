# Correlated Bernoulli sources and trimming

## Does the counting chain coincide with the older model?

### Takeaway

The transition rule agrees exactly when `p = 1/2` and `theta = a = 1 - 2 epsilon`. The conventional nonnegative-dependence range covers `0 < epsilon <= 1/2`, including the entire superdiffusive regime. The initial bias is a separate parameter.

### Cited findings

- James, James and Qi specify the transition probability `(1-theta_j)p + theta_j S_j/j` on p. 2339 and attribute the model to Drezner and Farnum. Their Theorem 2.2 includes an almost-sure limit when the squared reciprocal normalizers are summable. Their first page attributes the constant-parameter limit regimes to Heyde. [Full author copy](https://www.d.umn.edu/~yqi/mydownload/08letter.pdf)
- The manuscript now cites all three papers and states the model identification in the prior-work subsection. [Revised introduction](../../kagey-problems/problem131/paperD/sec_intro.tex)

### Inferences

Direct substitution gives

\[
(1-\theta)p+\theta b/t
=\tfrac12\{1-(1-2\varepsilon)\}+(1-2\varepsilon)b/t
=\varepsilon+(1-2\varepsilon)b/t.
\]

For a fair first step, initialization also agrees. Changing the initial bias changes the initial distribution without changing `p = 1/2` in the transition rule. Taking `p` equal to the initial bias would change the process itself.

The normalizer in the constant-parameter case is

\[
b_n=\prod_{j=1}^{n-1}(1+a/j)
=\frac{\Gamma(n+a)}{\Gamma(n)\Gamma(1+a)}
\sim\frac{n^a}{\Gamma(1+a)}.
\]

Thus `(A_n-n/2)/b_n -> V` corresponds to
`(2 A_n-n)/n^a -> 2 V/Gamma(1+a)`. The threshold `theta = 1/2` is the elephant copying threshold `1-epsilon = 3/4`. These are algebraic identifications, not additional asymptotic theorems.

### Gaps

The original Drezner–Farnum full text remains subject to the user's pending library request. The transition identification can already be checked from the later full paper, but finite-modality priority cannot. [Drezner–Farnum publisher record](https://doi.org/10.1080/03610929308831202)

## Which sources were read and what remains unchecked?

### Takeaway

James, James and Qi was read in full. Heyde's full text remains unavailable; the precise attribution is independently recorded in James, James and Qi's introduction.

### Cited findings

| Source | Reading completed in this pass | Use |
| --- | --- | --- |
| [James, James and Qi (2008), *Statistics & Probability Letters* 78, 2339–2345](https://doi.org/10.1016/j.spl.2008.01.104) | All seven pages, including the three main theorems, corollaries, proofs and references, from the [author PDF](https://www.d.umn.edu/~yqi/mydownload/08letter.pdf) | Exact model identification; fixed-parameter historical attribution; time-varying dependence result. No density-mode theorem is stated. |
| [Heyde (2004), *Australian & New Zealand Journal of Statistics* 46, 53–57](https://doi.org/10.1111/j.1467-842X.2004.00311.x) | Publisher abstract and [ANU bibliographic record](https://researchportalplus.anu.edu.au/en/publications/asymptotics-and-criticality-for-a-correlated-bernoulli-process/), not the five-page full text | The published abstract confirms the critical dependence split. The superdiffusive almost-sure limit is explicitly attributed to Heyde by the later full paper. |
| [Drezner and Farnum (1993), *Communications in Statistics—Theory and Methods* 22, 3051–3063](https://doi.org/10.1080/03610929308831202) | Previously checked publisher record and abstract; full text still pending | Model origin only. No priority claim about a universal mode bound. |

### Inferences

The manuscript should distinguish older fixed-parameter limit theory from its shape classification and rare-reversal estimates. Its revised paragraph does so without claiming the model or the superdiffusive convergence is new. [Revised introduction](../../kagey-problems/problem131/paperD/sec_intro.tex)

### Gaps

The Wiley PDF and full-text endpoints could not be retrieved. The [ANU repository record](https://openresearch-repository.anu.edu.au/items/868e7769-4bf3-4ba3-8301-e485749260a4) exposed metadata but no accessible paper. A full reading of Heyde is still needed before reporting that comparison as complete. No request or message was sent to anyone.

## What was shortened and preserved?

### Takeaway

The introduction is 396 whitespace-counted words shorter, including the added historical paragraph. Three bibliography entries were added. Page savings must be measured after the final combined revision is typeset.

### Cited findings

- Removed repeated framing and shortened descriptions of the model, comparison literature and article organization. All existing introduction theorem environments and displayed formulas remain byte-identical. [Edit checker](check_literature_edits.py), [recorded result](literature-edit-checks.json)
- Preserved the epigraph, its callback and the disclosure. The disclosure SHA-256 is `ed20652c6d4be4b2b4eab60960d73bbd0a1b1487f596bd7a8de6fb506288593d`. [Recorded check](literature-edit-checks.json)
- Only `sec_intro.tex` and the bibliography section of `problem131_memory.tex` were edited by this literature pass. [Introduction](../../kagey-problems/problem131/paperD/sec_intro.tex), [main source](../../kagey-problems/problem131/paperD/problem131_memory.tex)

### Inferences

The cut reduces repetition without moving results or proofs out of the paper. The remaining open-transition and open-bias sentences were left for the mathematical work to resolve.

### Gaps

The preservation checker records the introduction before any later theorem strengthening. If a later pass intentionally changes a theorem, its baseline equality check will fail and must not be reported as a final whole-revision check. The new bibliography entries also need the final LaTeX citation check.
