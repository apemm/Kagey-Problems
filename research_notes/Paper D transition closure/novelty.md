# Paper D modal classification novelty check

Audit date: 2026-11-01. This is a targeted comparison for the centred interval of bimodal initial biases and the unique fair-start shape transition. It is not an exhaustive priority search.

## Does the bias theorem resolve the stated GLRS conjecture?

### Takeaway

Yes, the theorem's endpoint convention matches the conjecture exactly. The result is stronger than the requested near-one statement because it applies throughout the superdiffusive parameter range.

### Cited Findings

- GLRS Remark 2.1(b) conjectures that, for each memory parameter `a` in `(1/2,1)`, a radius `q(a)` in `[0,1/2]` separates bimodal biases `|q-1/2| < q(a)` from unimodal biases `|q-1/2| >= q(a)`. Equality belongs to the unimodal case. Their conditional result concerns the endpoint bias `q=1`. [GLRS, Section 2 and Remark 2.1(b)](https://arxiv.org/html/2409.06836v1#S2)
- The project's classification gives an endpoint `b(a)` in `[0,1/2]`, exactly two local maxima precisely when `b(a) < q < 1-b(a)`, and a unique unimodal maximum otherwise. It derives the required half-line restriction from the finite counting recurrence and transfers it through the local limit theorem. [Formal assembly](../../kagey-problems/problem131/lean/PaperD/Modes/BiasIntervalAssembly.lean), [generic classification](../../kagey-problems/problem131/lean/PaperD/Modes/BiasMixtureIntervalModes.lean)

### Inferences

- Set `q(a)=1/2-b(a)` to recover the conjecture's statement, including a possibly empty interval. Thus “resolves the conjecture in GLRS Remark 2.1(b)” describes the proved mathematical implication.
- This comparison does not prove that no other author has resolved the conjecture. The priority assessment remains bounded by the search and reading record below.
- The theorem does not establish continuity or monotonicity of `b(a)` in `a`. It also does not establish `b(a)>0` for every fixed `a<1`.

### Gaps

- The fresh pass used the authors' arXiv text. It did not repeat a page-by-page comparison with the publisher PDF. [Published record](https://doi.org/10.1214/25-EJP1362)

## Do the later local-limit and shape papers already establish these results?

### Takeaway

Trinas and Valle address a different conjecture, concerning log-concavity at endpoint bias. Their local limit theorem is an input to the new classification, not a competing classification.

### Cited Findings

- Trinas and Valle's Theorem 3.1 proves the span-two uniform local limit theorem for all initial biases. Section 4 then restricts to `q=1` and studies eventual log-concavity, corresponding to GLRS Remark 2.3. Its thresholds concern log-concavity, not the fair-start change in the number of modes. Their Section 5 contains finite-row log-curvature computations. The paper does not state a centred bimodal-bias interval theorem or uniqueness of the fair-start modal transition. [Trinas and Valle, Sections 2–5, arXiv v1](https://arxiv.org/html/2609.14753v1)
- The current Peres–Qin abstract and opening describe upper transition-probability bounds on groups and nonamenable Cayley graphs. These are different targets from one-dimensional modal classification. [Peres and Qin, arXiv v2](https://arxiv.org/html/2604.07227v2)
- Gut and Stadtmüller's abstract and introduction concern a Bernoulli variant motivated by walks with stops and restricted memory. [Gut and Stadtmüller, abstract and introduction](https://link.springer.com/article/10.1007/s10959-026-01517-1)
- Fang's abstract and introduction concern initial training and return-time scales, especially the diffusive and critical regimes. [Fang, abstract and introduction](https://link.springer.com/article/10.1007/s10955-026-03646-7)

### Inferences

- The new half-line sign argument has a distinct role from the local limit theorem: it constrains where modes can occur before using convergence to pass the constraint to the density.
- Avoid comparing the certified fair-start threshold with the later paper's log-concavity threshold as if they measured one transition.
- The inspected later sources do not displace the two proposed modal results. Only the Trinas–Valle paper received a complete fresh mathematical-text reading in this pass. The other later papers received relevance screening, not complete exclusion by theorem audit.

### Gaps

- The pending Drezner–Farnum full text remains relevant to the counting-chain lineage. This audit does not close that comparison. The correlated-Bernoulli comparison is recorded separately in [literature.md](literature.md).
- No citation index was exhaustively enumerated. Unindexed manuscripts and private work are outside this search.

## What was actually read and searched?

### Takeaway

The targeted searches found no later primary source resolving either modal claim through the audit date. That is a search result, not proof of absence.

### Cited Findings

| Source | Fresh reading scope | Status |
|---|---|---|
| [GLRS, arXiv v1](https://arxiv.org/html/2409.06836v1) | Introduction, conditional-unimodality proof, Remark 2.1, and relevant adjacent statements | Targeted sections read. Whole paper not reread. |
| [Trinas–Valle, arXiv v1](https://arxiv.org/html/2609.14753v1) | Abstract, all mathematical Sections 1–5, statements, proofs, discussion, and references | Mathematical text read in full through HTML. Code not inspected or rerun. |
| [Peres–Qin, arXiv v2](https://arxiv.org/abs/2604.07227) | Current abstract, version record, introduction, and model definition | Partial reading only. |
| [Gut–Stadtmüller, JTP 2026](https://link.springer.com/article/10.1007/s10959-026-01517-1) | Abstract and relevant opening paragraphs | Partial reading only. |
| [Fang, JSP 2026](https://link.springer.com/article/10.1007/s10955-026-03646-7) | Abstract and opening motivation/model | Partial reading only. |

### Inferences

- Search strings combined the exact GLRS identifier and author names with “bimodal”, “bimodality”, “Remark 2.1”, “unimodality”, “centered interval”, “modal transition”, and “0.6688”. Separate searches checked the Trinas–Valle identifier and 2026 elephant-walk results.
- Results were screened against the primary arXiv and publisher pages linked above. Secondary summaries were not used to establish technical claims.
- Suggested manuscript wording: “We prove the conjecture of Guérin, Laulin, Raschel and Simon in Remark 2.1(b).” The conclusion should identify the conjecture directly rather than add an unqualified “first” claim.
- Suggested research-report wording: “A targeted literature search through 1 November 2026 found no later resolution of the centred bias-interval conjecture or the unique fair-start modal transition.”

### Gaps

- This pass did not reread all earlier cited papers. Prior reading records retain their own scope and should not be upgraded to fresh full-text checks.
- HTML reading does not independently validate third-party numerical certificates. The claim here concerns the stated results and mathematical scope of the compared papers.
