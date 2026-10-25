# 20. Deep edit of Paper C1 for JTP

October 24, 2026. An editing pass on Paper C1 (`kagey-problems/problem131/paperC`) to make it
concise and focused for the Journal of Theoretical Probability, after reading README, EXPORTS and
audits 10, 13 and 19, and then the whole paper. Nothing outside `paperC`, this note and
`18_arxiv_form_C1.txt` was edited. `paperC2` was not touched.

Result: the article build went from 67 to 59 pages and the Springer build from 72 to 65. No
theorem, proposition, lemma or corollary statement changed, and no proof lost a step. The words in
the sources went from 32186 to 27635.

## 1. Framing

The new first paragraph of the introduction:

> Let $Q$ be a generator on $d$ states, and run the chain for $N$ steps with transition matrix
> $I+(T/N)Q$. It then makes about $T$ switches, and we let $T$ range from $1$ to $N^{1/3}$. The
> occupation counts $n_i=\#\{t\le N:X_t=i\}$ have support $F=\{i:n_i>0\}$, which is a face of the
> simplex. We describe the law of the count vector on every face. Inside a face it is a local limit
> law with an explicit constant. Its exponent is the lattice entropy $(|F|-1)\log N$ of the face
> plus $T$ times the Donsker and Varadhan cost of the point, and this cost is one functional of the
> whole chain. Near a facet the law on the face is the law on the facet times an explicit kernel.
> The most likely count vector, the mode, lies on the face where this law is largest. A crossing is
> a value of $T$ at which the mode changes face. When $T=\tau\log N$ the law locates every
> crossing.

So the law comes first, the face of the mode is its consequence, and a crossing is defined as a
change of the mode in the first paragraph.

- The introduction now opens with the theorem a probabilist would cite. Theorem A is the law on a
  face: the stratified local law (Theorem 5.6) and the face maxima (Theorem 5.7 at $v=0$), both
  uniform for $1\le T\le N^{1/3}$. Theorem B is the support of the mode: first-order selection
  (Theorem 4.2(ii) to (iv)) and the crossing equation (Theorem 5.8). Theorem C, the complete
  graph, is unchanged. Each introduction theorem says the same as the body theorems it
  collects. In Theorem B(i) the condition "the chain can pass between any two states of each
  minimizing face" is now written "each such minimizing face satisfies (H)", which is the same
  condition for an admissible face by Lemma 2.2(b).
- The boundary layer has its own subsection of the introduction (1.2), shortened.
- Kagey's Problem 131 is mentioned once, in the acknowledgments: "The question grew out of
  Problem 131 of Peter Kagey's Open Problem Collection [kagey131], and I thank him for posing it."
  It is gone from related work. It was never in the title, abstract or first paragraph.
- No series language. The companion paper is one sentence: "A companion paper [paperC2] asks
  what the Donsker and Varadhan functional and the modal supports determine about the
  generator." Section 5.5 cites [paperC2] once more, without the word companion, to say why its
  set of fields is the one fixed there. Paper A is cited where its results are used: Lemma 3.2(b)
  in Appendix D, the next term for two states after Theorem 7.4, the fixed-edge expansion after
  Theorem 8.2, and the walk itself in Example 2.5(i). The paragraph that listed what we take from
  Paper A is gone.
- The "As on a Galton board ... bin" sentence is deleted with the rest of the two-state walk
  paragraph of Section 2. "Bin" no longer occurs. "Row" occurs only for rows of matrices, which
  is the standard term there.
- The `\ifarxivbuild` switch is unchanged. The related-work paragraph still says "replaces our
  preprint ... which is the first version of the same arXiv entry" in the article build and
  "supersedes our preprint" in the Springer build, and `\Bversion` still reads "the first
  version" or "the preprint".

### Title

Chosen: "Occupation counts of rarely switching Markov chains: stratified local laws, support
selection and the boundary layer". The main title is kept. "Support selection" names what the
paper decides about the mode, and it fits the new first paragraph.

Alternatives considered:
1. "Occupation counts of rarely switching Markov chains: local laws on faces, support selection
   and the boundary layer". Plainer, but "stratified" is the term the paper uses for Theorem 5.6.
2. "Occupation counts of rarely switching Markov chains: stratified local laws and support
   selection". Shorter, but it hides the facet theorem, which is half of the new work.

The title is changed in both main files, the cover letter, README, EXPORTS and the arXiv form.

## 2. Cuts

Article pages, estimated from the words removed (about 470 words a page) and checked against the
builds: 67 pages before, 64 after the first pass, 61 after the tree formula and Figure 4, 60
after Section 7.1, 59 after small trims.

| Cut | Pages |
|---|---|
| The tree formula on a general face, Proposition 5.11 with Section 5.4, and its appendix lemma, Lemma A.5 with Appendix A.7. The two bibliography entries used only there (Tutte, Chaiken) and the macro `\arb` went too. See below for the dependencies. | about 2.3 net |
| Section 7.1, the pair identity (Proposition 7.1) and the two-state corollary (Corollary 7.2), with the two-state walk paragraph of Section 2 that defined $S_{a,b}$, $S_N$, $u_N$, $p_N$, $z_N$, $c_0$. Corollary 7.2 is the case $d=k=2$ of Theorem 7.4, and Proposition 7.1 was used only for Corollary 7.2. A sentence after Theorem 7.4 keeps the link to the persistent walk and $a_2=\frac12\log(\pi/8)$. The recalled expansion of $z_N$ in Section 2 duplicated the sentence on the next term after Theorem 7.4, which stays. | about 0.9 |
| Remark 7.4, first-order winners on other graphs. Its first half restated Corollary 7.3, and nothing used the rest. | about 0.5 |
| The restatement of the local law on the complete graph, equation (21) with its paragraph. It was Theorem 5.4 with Example 7.2, and one sentence now says so and cites [paperB, Theorem 3.3]. | about 0.35 |
| Figure 4 (the 6-cycle hull and the modes on $C_5$). The 4-cycle figure shows the same hull, and Figure 2 shows finite-$N$ modes. The figure has 3 figures now. | about 0.4 |
| Section 6.7: the numerics paragraph (now one paragraph of Section 9, where the same scripts were already described) and the open-problem paragraph (now the last sentence of Section 9). The lattice comparison moved to Section 8, after Theorem 8.2, where its notation is defined. | about 0.35 |
| Every scattered sentence on Lean (after Lemma 2.3, Proposition 3.3, Theorem 4.4, Example 5.11, Proposition 7.1, Corollary 7.3, Remark 7.7). Section 9 lists all of them. | about 0.4 |
| Previews and restatements: the openings of Sections 3, 5 and 6 (shortened to what they claim), the paragraph after Theorem 5.6 on the boundary, "Part (b) needs a reversible face", the sentence on what $\mu\cdot r_\alpha$, $l_\alpha\cdot\ones$ and $\Sigma_\alpha$ account for (said before Definition 5.1), the restatement of Proposition 3.3(a) and (d) after it, the "in words" sentences after Theorems 5.8 and Lemma A.2, the sentence after Example 5.11 that repeated the opening of Section 5.4, the restatement of the cost competition after Proposition 3.1, the Rayleigh and Ritz aside after Theorem 4.4. | about 1.2 |
| Idea-of-proof paragraphs placed right before the proof they summarize: Theorem 5.7, Lemma B.1, Lemma 5.5 (Appendix A.5). The sketch of Theorem 4.2(ii) in the main text duplicated the idea paragraph of Appendix A.6 and its proof, so the main text now points to the appendix and the appendix keeps a short idea paragraph. The idea of Theorem 5.4 stays, since its proof is in the appendix. | about 0.7 |
| Introduction: Good's formulas and the exponents (said in Section 2), the plan paragraph (now two sentences), the list of results taken from Paper A, the companion paragraph (one sentence), related work tightened. Good's saddle-point remark after Theorem 5.4 went, since the introduction says it. | about 0.7 |
| Code availability: what Section 9 already says about running the scripts. | about 0.15 |
| Remark 7.7 (the counterexample at $N=4$) written without a display, the same content. | about 0.1 |

Added: the direct computation of $K_{\{1,2,3\}}$ in Example 5.11 (about 0.25 page), Theorem A
in the introduction, and the lattice paragraph in Section 8 (moved, not new).

### The tree formula and its dependencies

Proposition 5.11 was used only in Example 5.14 (now 5.11), part (i), for the value
$K_{\{1,2,3\}}=(1+2b)^2/(2\sqrt3\,\pi b)$. The example now computes this value in its proof with
every step: by the arithmetic and geometric means $J_V(\alpha)=b\alpha_1+\alpha_2+\alpha_3-3\phi$
with $\phi=(b\alpha_1\alpha_2\alpha_3)^{1/3}$, the Hessian in $(\alpha_2,\alpha_3)$ at
$\alpha^*=(c,bc,bc)$ is $\frac{1+2b}{3b}$ times the matrix with diagonal $2b^2+2b+2$ and
off-diagonal $2b^2+2b-1$, its determinant is $(1+2b)^4/(3b^2)$, and Proposition 5.2(a) gives
$\det\Sigma_{\alpha^*}=3b^2/(1+2b)^4$. The Hessian and the determinant were checked
symbolically. The statement of the example is unchanged. The weighted Cayley formula and the
complete face, which sat in the same subsection and are used only in Section 7, moved to the start
of Section 7 (now Lemma 7.1 and Example 7.2). The introduction sentence "on a general face two
counts of trees" went. `verify_forest.py` stays and still passes. It now checks a formula the
paper no longer states, which README records.

EXPORTS.md listed `lem:forest` in its table of statements not cited by paperC2. The task allowed
this cut with its appendix, so it is removed and recorded in EXPORTS. paperC2 cites none of it.

Considered and not cut: Remark 7.7 (it shows that Corollary 7.6 needs large $N$), Figure 2 (the
only picture of the law on the simplex), Section 4.1 with its figure (the 4-cycle is used again in
Section 5.3), Lemma 6.7 for two states (listed in EXPORTS). Kept as required: Section 3.2 with
Proposition 3.4, Section 5.5 with Proposition 5.12 (statement word for word, label kept),
Section 8 and Appendix D, Section 6 with the general facet theorem and Lemmas A.3, A.4, B.3,
Example 5.11, and every statement in EXPORTS other than `lem:forest`.

## 3. Voice pass

Over all sections: no semicolons or em-dashes were found in the prose, and none were added. Step
headings "Step 1: the series." became "Step 1. The series." (19 places). Parentheticals that
carried content became sentences (Lemma 2.2 twice, Section 2.1, Section 4.1, Theorem 5.9, the
proof of Proposition 5.12, Appendix A three times, Appendix C, Example 7.2). "Note that",
"recall" and "now we" are gone (8 places). British spellings were made American (neighbors,
neighborhood, favors). Hype: "insightful" left the acknowledgments. Sentences over about 40
words in prose were split where they were not theorem statements (Section 6.1, Section 7, Appendix
C).

- Section 1. Rewritten around the law, with Theorem A first, short sentences, one idea each.
  Related work about a third shorter.
- Section 2. The parenthetical on the scalar $q$, the two-state walk paragraph and the Lean
  sentence went. Good's two formulas are attributed once each, in one or two sentences.
- Section 3. The opening is one sentence. The comments after Propositions 3.1 and 3.3 keep only
  what is new.
- Section 4. The 4-cycle heuristic is one sentence shorter (the fluctuation scale is in the
  introduction). The proof of (ii) points to the appendix. The paragraph after Theorem 4.4 is
  five plain sentences.
- Section 5. Opening list, Good remark, the idea paragraph of Theorem 5.7 and the "in words"
  paragraph after Theorem 5.8 went. Remark 5.10 keeps two points. Section 5.5 opens in three
  sentences.
- Section 6. The opening paragraph keeps the qualification asked for by audit 10 (prefactor
  match only for reversible $Q$) in five sentences. Comments after Proposition 6.3 and Theorem
  6.6 shortened, one long sentence split.
- Section 7. One subsection now. The heuristic before exact balancing moved after the theorem,
  as part of the sentence on the proof, so it is said once.
- Section 8. The opening is two sentences, and the lattice paragraph from Section 6.7 follows
  Theorem 8.2.
- Section 9. Holds the numerics once and the open questions once.
- Appendices. Idea paragraphs that repeated the proof that follows went, and the steps use
  periods.

## 4. Abstract, cover letter, README

The abstract has 247 words by `wc` (1420 characters) and states the local law with its range and
error, the restriction identity, first-order selection, the crossing location with the $\frac12$
coefficient, the facet kernel with its three regimes and the three complete-graph results. It is
the same in both main files and is pasted into `18_arxiv_form_C1.txt`, since
`18_abstract_C1.txt` is outside the scope of this edit and still holds the earlier abstract.
The cover letter opens with the law and uses the new title. It says that the paper uses one lemma
of Paper A (it used two before Section 7.1 went). README is rewritten with the new numbers, the
history entry and the labels removed.

## 5. Renumbering of exported statements

| Label | Before | After |
|---|---|---|
| `prop:uniform-facemax` | Proposition 5.15 | Proposition 5.12 |
| `sec:uniform-class` | Section 5.6 | Section 5.5 |
| `eq:A-radii` | (29), Springer A3 | (28), Springer A3 |
| `lem:forest` | Lemma A.5 | removed |

Every other label in EXPORTS keeps its number in both builds (checked in the `.aux` files):
Definitions 2.1 and 5.1, Lemmas 2.2 to 2.4, 3.2, 4.1, 5.5, 6.7, 6.8, A.2 to A.4, B.1, B.3,
Propositions 3.1, 3.3, 3.4, 5.2, Remark 4.3, Theorems 4.2, 4.4, 5.4, 5.6 to 5.8, 6.6, 6.9,
Section 3.2 and equations (1), (6), (9), (19). For paperC2 the only change to make is
`\cite[Proposition~5.15]{paperC1}` in `sec_reversible.tex` to Proposition 5.12, and Section 5.6
to Section 5.5 if it is named. paperC2 cites the title of C1 in its bibliography, which should
become the new title.

Other numbers that moved (not exported), for `lean/PaperC/MAP.md` and the scripts' docstrings:
Example 5.14 is 5.11, Lemma 5.12 is 7.1, Example 5.13 is 7.2, Theorem 7.5 is 7.4, Theorem 7.6 is
7.5, Corollary 7.7 is 7.6, Remark 7.8 is 7.7, Section 5.5 is 5.4, and Section 7.2 is Section 7.
Removed: Proposition 5.11, Proposition 7.1, Corollary 7.2, Remark 7.4, Lemma A.5, Figure 4,
equation (21). In the article build the old equations (22) to (39) are now (21) to (38). The
Springer appendix equations are unchanged (A1 to A7, C1, C2, D1 to D4). Corollary 7.3 and all of
Sections 2 to 4, 6 and 8 and Appendices B to D keep their statement numbers.

## 6. Builds and scripts

- `problem131_chains.tex`, built 4 times: 59 pages. No undefined reference or citation, no
  multiply defined label, no overfull box.
- `problem131_chains_sn.tex` with `TEXINPUTS=".;../common/sn-jnl;"`, built 4 times: 65 pages,
  with the same checks clean.
- `py -I verify_all.py --quick`: 7 of 7 scripts passed in 504 s. The outputs in `data/` were
  rewritten by the run with their sha256 headers. No script was edited, so no hash changed.
- The auxiliary files and `__pycache__` were deleted after the builds, and both PDFs kept.

Files outside the write scope that now need a sync: `paperC2` (one number and the title),
`lean/PaperC/MAP.md` (the numbers above and the removed statements), the top-level
`problem131/README.md` (title, page counts) and `18_abstract_C1.txt` (the new abstract is in the
form file).
