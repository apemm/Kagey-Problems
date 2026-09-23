# Checked sources for the binary crossing paper

## What does Dekking–Kong Proposition 4.3 establish?

### Takeaway

Interior log-concavity is prior work for the entire nondegenerate symmetric parameter range. It should be cited as an ingredient, not presented as a new theorem. [Dekking–Kong, Section 4, Proposition 4.3](https://arxiv.org/pdf/1102.3613#page=12)

### Cited Findings

- The paper assumes `0<a,b<1`, initial distribution `nu=(nu_S,nu_F)`, and transition matrix `[[1-a,a],[b,1-b]]`; `K_n` counts successes in `n>=1` observations. No stationarity assumption is imposed. [Section 1, p. 1](https://arxiv.org/pdf/1102.3613#page=1)
- Proposition 4.3 states log-concavity of `(f_n(1),...,f_n(n-1))`. The following paragraph states the strengthening `f_n(j)^2 > f_n(j-1)f_n(j+1)` for `j=2,...,n-2`, obtained by sharpening Lemma 4.2. The proposition's displayed proof gives the non-strict result. [Section 4, p. 12](https://arxiv.org/pdf/1102.3613#page=12)
- The condition `a+b>=1` belongs to Proposition 4.2, concerning the full sequence including endpoints; it is not a condition of Proposition 4.3. [Section 4, p. 9](https://arxiv.org/pdf/1102.3613#page=9)

### Inferences

- Setting `a=b=1-p`, `nu=(1/2,1/2)`, and `n=N` covers every `0<p<1` here. Symmetry and strict interior log-concavity locate the interior maxima at the central bin or pair; they do not determine the crossing parameter with the endpoints. [Proposition 4.3 and its following paragraph](https://arxiv.org/pdf/1102.3613#page=12)

### Gaps

- The boundary parameters `p=0,1` require separate treatment; the cited assumptions exclude them. [Section 1](https://arxiv.org/pdf/1102.3613#page=1)

## What does Stepanyan et al. equation (16) claim?

### Takeaway

The periodic endpoint–center comparison is an explicit antecedent. Equation (16) is presented as an approximation, without a proved asymptotic remainder. [Section III.B, p. 3](https://arxiv.org/pdf/2307.15479v3#page=3)

### Cited Findings

- The model has Hamiltonian `H=-J sum sigma_j sigma_(j+1)-h sum sigma_j`, ferromagnetic `J>0`, and periodic boundaries. Section III.B sets `h=0`. [Sections II–III.B](https://arxiv.org/html/2307.15479v3#S3.SS2)
- Equation (16) follows the equality `P_(m=±N)=P_(m=0)` and the words “to a good approximation”: `beta_tr^(2) ≈ [2 log N-1]/(5J)`. Figure 1(b)'s caption separately gives `beta_tr^(2) J ≈ 0.3864 log N-0.21055`. [Equation (16) and Figure 1, p. 3](https://arxiv.org/pdf/2307.15479v3#page=3)
- The following paragraph describes each ferromagnetic probability as that of a single configuration, compared with the whole zero-magnetization bin. [Immediately after equation (16)](https://arxiv.org/html/2307.15479v3#S3.E16)

### Inferences

- The comparison with `m=0` concerns even `N`, by magnetization parity. The manuscript may distinguish its proved large-`N` expansion from this approximation, but should not claim discovery of the crossing question. [Model and equation (16)](https://arxiv.org/pdf/2307.15479v3#page=3)

### Gaps

- Neither equation (16) nor its neighboring discussion specifies an asymptotic error bound or a uniform validity range. The displayed approximation must not be relabeled as a rigorous leading asymptotic. [Section III.B](https://arxiv.org/html/2307.15479v3#S3.SS2)

## What do the official journal pages say about length?

### Takeaway

Statistics & Probability Letters advertises a six-journal-page limit. Journal of Applied Probability has inconsistent numerical guidance across its two official sites; both preserve editorial discretion over allocation to its companion journal. [Elsevier description](https://shop.elsevier.com/journals/statistics-and-probability-letters/0167-7152), [Cambridge instructions](https://www.cambridge.org/core/journals/journal-of-applied-probability/information/author-instructions), [Applied Probability Trust](https://www.appliedprobability.org/author-information)

### Cited Findings

- Elsevier's current journal description limits articles to six journal pages, described as 13 double-spaced typed pages, including figures and references. It also allows abbreviated proofs when adequate supporting material permits verification. [Elsevier, Description](https://shop.elsevier.com/journals/statistics-and-probability-letters/0167-7152)
- Cambridge's author instructions specify research papers of at most 25 printed pages. Submissions are considered for both JAP and AAP, with allocation by the Executive Editor. [Cambridge, Publishing policy and Scope](https://www.cambridge.org/core/journals/journal-of-applied-probability/information/author-instructions)
- The Applied Probability Trust's own author page instead gives a current rule of thumb of 1–30 pages for JAP and 31 or more for AAP, noting that length is only one allocation factor. [APT, Scope of the journals](https://www.appliedprobability.org/author-information)

### Inferences

- A manuscript's present LaTeX page count is not itself its journal page count. These length statements neither establish editorial suitability nor predict acceptance. The conflicting JAP numbers should be reconciled before planning to either numerical cutoff. [Cambridge instructions](https://www.cambridge.org/core/journals/journal-of-applied-probability/information/author-instructions), [APT author information](https://www.appliedprobability.org/author-information)

### Gaps

- The ScienceDirect Guide for Authors could not be retrieved; the SPL finding is supported by the publisher's accessible journal description. No exception to its stated limit was verified. [ScienceDirect guide](https://www.sciencedirect.com/journal/statistics-and-probability-letters/publish/guide-for-authors), [Elsevier description](https://shop.elsevier.com/journals/statistics-and-probability-letters/0167-7152)
- The official JAP sites do not explain the discrepancy between 25 printed pages and the 30-page allocation guideline. [Cambridge](https://www.cambridge.org/core/journals/journal-of-applied-probability/information/author-instructions), [APT](https://www.appliedprobability.org/author-information)

## What does the full Renshaw–Henderson paper establish?

### Takeaway

The full text of Renshaw and Henderson (1981), *The correlated random walk*, pp. 403–414, was read through authenticated JSTOR. Its exact law and Bessel limits are direct antecedents. [Full article](https://www.jstor.org/stable/3213286)

### Cited Findings

- The model uses continuation probability `p`, reversal probability `q=1-p`, and an unbiased initial direction. Its motivation includes a Galton-style pinball machine. Equation (2.1) gives the run-count law; (2.6)–(2.8) give generating-function and even/odd formulas. [pp. 403–407](https://www.jstor.org/stable/3213286?seq=1)
- Page 408 discusses endpoint upturns. Section 3 derives the diffusion approximation. [pp. 408–410](https://www.jstor.org/stable/3213286?seq=6)
- Section 4 fixes `p^n=exp(-mu)` while `n` grows; equation (4.4) gives the interior Bessel limit for `2n` steps. Page 412 identifies its unique interior maximum. Equation (4.6) subsequently expands this limiting expression as `mu` grows. [pp. 410–413](https://www.jstor.org/stable/3213286?seq=8)

### Inference and remaining distinction

These are fixed-scaling and sequential large-parameter limits. Substituting a growing `mu` of logarithmic order requires additional uniform control. This paper contains no finite-`N` crossing uniqueness/order theorem or uniform moving-parameter crossing expansion. Those distinctions support our narrower claims; they do not establish novelty across the literature. [Section 4](https://www.jstor.org/stable/3213286?seq=8)
