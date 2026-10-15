# JSTAT exemplars: how exact and rigorous results on random walks and 1D chains are presented

Method note: I checked every journal reference against arXiv metadata (export.arxiv.org API `journal_ref` / DOI fields). A DOI prefix of `10.1088/1742-5468` means JSTAT. I downloaded the arXiv LaTeX source of 14 JSTAT papers and parsed it: abstract, section list, theorem environments (`\newtheorem`, `\begin{theorem}`, `\begin{proof}`), figure count, appendix placement, bibliography size, and which mathematical sources are cited. Page counts are for the **arXiv versions** (taken from the arXiv comment field or a count of PDF pages), not the typeset JSTAT versions. iopscience.iop.org blocked automated access (Radware bot check), so I could **not** read the official JSTAT keyword lists on the article pages. See the Gaps sections.

---

## Q1. Catalogue of exemplar JSTAT papers (2015-2025): citation, length, abstract, motivation, packaging, figures, math citations, keywords

### Takeaway
I verified 14 papers as published in JSTAT and grouped them into three families.
- **Physicist exact-solution style.** The large majority: Majumdar/Schehr/Mori/Dhar/Sabhapandit/Kundu, Godrèche/Luck, Evans, Rossetto, Gastner. No theorem environments. Results are "derived", checked against simulations in figures, and long computations go to appendices. Usually 20-36 pp, 3-11 figures.
- **Mathematical-physics hybrid.** Artuso et al. Prose with "Theorem" used only informally.
- **Probabilist Theorem/Proof style.** Coletti et al. (x2), Mailler and Uribe Bravo. Full `\newtheorem` sets, a "Main results" section followed by a "Proofs" section, and no figures or numerics. This style exists in JSTAT but is a minority.

### Cited Findings

**Family A: exact results presented physics-style (no theorem environments)**

1. **Malakar, Jemseena, Kundu, Vijay Kumar, Sabhapandit, Majumdar, Redner, Dhar, "Steady state, relaxation and first-passage properties of a run-and-tumble particle in one-dimension", J. Stat. Mech. (2018) 043215.** arXiv:1711.08474. 26 pp (arXiv PDF).
   - **Abstract.** 143 words, all first-person-plural results statements: "We investigate the motion of a run-and-tumble particle (RTP) in one dimension. We find the exact probability distribution of the particle with and without diffusion on the infinite line, as well as in a finite interval. ... Finally we compute the survival probability of the RTP in a semi-infinite domain ... We provide numerical verification of our analytical results."
   - **Introduction.** Opens with active matter (bacteria, flocking, granular matter, motility-induced phase separation, absence of an equation of state for active pressure), then frames RTPs as the "simplest examples".
   - **Packaging.** Sections: Introduction / RTP Model / Occupation probability (infinite domain; bounded interval) / First-passage properties / Summary, plus 4 appendices that hold the finite-interval solutions. No theorem/lemma/proof environments. "We find" appears 14 times.
   - **Figures.** 8. The captions present them as checks, e.g. "Comparison of the steady-state probability density ... with explicit Langevin simulations ... using 10^6 different realizations."
   - **References.** 57, mostly physics. Orsingher is cited (2 hits); no Feller, Ann. Probab. or J. Appl. Probab.
   - Sources: [arXiv:1711.08474](https://arxiv.org/abs/1711.08474), [DOI search hit](https://arxiv.org/abs/1711.08474) (journal_ref JSTAT/2018/043215).

2. **Singh and Kundu, "Generalised 'Arcsine' laws for run-and-tumble particle in one dimension", J. Stat. Mech. (2019) 083205.** DOI 10.1088/1742-5468/ab3283. 32 pp, 15 figures (arXiv comment).
   - **Abstract.** 190 words. It starts from the classical result ("The 'Arcsine' laws of Brownian particles in one dimension describe distributions of three quantities ..."), then states the new results ("We compute exact distributions of these three quantities for arbitrary time ...") and ends with "We verify all our analytical results through numerical simulations."
   - **Introduction.** Motivates through the history of the arcsine laws (Lévy, Feller), then lists many physics applications: constrained Brownian motion, queueing, fractional BM, finance, disordered systems.
   - **Packaging.** No theorem environments. Seven appendices, one of them titled "Proof of the identity", so the word "proof" is used for appendix derivations without formal environments.
   - **Figures.** 11 figure environments. The captions read "Numerical verification (filled circles) of the time evolution of the propagators ...".
   - Source: [arXiv:1906.09442](https://arxiv.org/abs/1906.09442).

3. **Mallmin, Blythe, Evans, "Exact spectral solution of two interacting run-and-tumble particles on a ring lattice", J. Stat. Mech. (2019) 013204.** DOI 10.1088/1742-5468/aaf631. 29 pp, 7 figures. This is the closest lattice and persistent-walk analogue to the author's paper.
   - **Abstract.** It opens with a field-level claim: "Exact solutions of interacting random walk models, such as 1D lattice gases, offer precise insight into the origin of nonequilibrium phenomena. Here, we study ... We present the exact solution for one and two particles using a generating function technique." It ends with a broader-relevance sentence about exceptional points in "open quantum systems and multichannel scattering".
   - **Introduction.** Starts from Einstein and Smoluchowski, moves to detailed balance and exactly solvable lattice gases (ASEP), and then explicitly identifies the RTP as "an example of a persistent random walker (PRW)" (citing Masoliver, Weiss).
   - **Packaging.** No theorem environments; 84 numbered equations. The appendices cover the asymptotic spectrum and the "Derivation of two-particle eigenvectors". No simulations: the figures show the spectrum and relaxation times computed from the exact solution.
   - Source: [arXiv:1810.00813](https://arxiv.org/abs/1810.00813).

4. **Mori, Gradenigo, Majumdar, "First-order condensation transition in the position distribution of a run-and-tumble particle in one dimension", J. Stat. Mech. (2021) 103208.** DOI 10.1088/1742-5468/ac2899. 24 pp, 10 figures.
   - **Abstract.** 162 words with the "We consider ... We show ... Our results are supported by numerical simulations performed with a constrained Markov chain Monte Carlo algorithm" pattern.
   - **Introduction.** Opens with active matter (birds, gels, bacteria), then notes that the RTP "was originally known as persistent random walk" (citing Kac 1974, Orsingher 1990, Weiss).
   - **Packaging.** Section 2 is "The model and the summary of the main results", so the main formulas are stated up front, physics-style. Nine appendices hold the asymptotics, the critical-point computation and the "Equivalence with the result of Ref. [BKL20]". No theorem environments; "we show" appears 9 times and "we find" 30 times.
   - **Figures.** Each figure overlays the theory line (solid) on simulations (dashed) for several N.
   - Source: [arXiv:2107.00338](https://arxiv.org/abs/2107.00338).

5. **Godrèche, Majumdar, Schehr, "Statistics of the longest interval in renewal processes", J. Stat. Mech. (2015) P03014.** DOI 10.1088/1742-5468/2015/03/P03014. 30 pp, 9 figures.
   - **Abstract.** Long (302 words) and technical. It states hypotheses carefully in prose ("We show that if ρ(τ) admits a well defined first moment ... then the full statistics ... is given, in the large t limit, by the standard theory of extreme value statistics").
   - **Introduction.** Renewal processes as "the simplest generalizations of the Poisson process" (Feller, Cox), with applications such as taxis at airports, phase ordering and blinking quantum dots. It explicitly positions the work against the probability literature: "Some aspects of this question were studied in the past by Lamperti ... Our aim is to perform a complete and thorough re-examination of this problem."
   - **Packaging.** Structured as Cases I/II/III, each with "Distribution / Probability of record breaking / Discussion", plus an appendix on notation and joint densities. No theorem environments; 3 tables.
   - Source: [arXiv:1412.7381](https://arxiv.org/abs/1412.7381).

6. **Hartmann, Majumdar, Schawe, Schehr, "The convex hull of the run-and-tumble particle in a plane", J. Stat. Mech. (2020) 053401.** DOI 10.1088/1742-5468/ab7c5f. 21 pp, 8 figures, 1 table.
   - **Abstract.** 138 words. "We study the statistical properties of the convex hull of a planar run-and-tumble particle (RTP), also known as the 'persistent random walk' ... we derive exact expressions for the average perimeter ... and then compare to numerical estimates finding excellent agreement. Further, we numerically compute the full distribution ... up to a precision smaller than 10^-100."
   - **Introduction.** Random walks (Chandrasekhar, Feller, Hughes), then correlated steps for animal movement and polymers, then active matter.
   - **Packaging.** Exact results for the mean are paired with heavy large-deviation Monte Carlo for the full distribution. Cites Spitzer and Kac (Cauchy formula). No theorem environments.
   - Source: [arXiv:1912.08778](https://arxiv.org/abs/1912.08778).

7. **Godrèche and Luck, "Maximum and records of random walks with stochastic resetting", J. Stat. Mech. (2022).** DOI 10.1088/1742-5468/ac6d60. The article number is not shown in the arXiv metadata; I believe it is 063202, but that is unverified. 36 pp, 6 figures.
   - **Abstract.** 133 words: "We revisit the statistics of extremes and records ... The exact solution of the problem for the symmetric exponential step length distribution and for the simple Polya lattice walk, as well as a heuristic analysis of other distributions, allow a quantitative study ...". Note how exact and heuristic results are labelled side by side.
   - **Introduction.** Very short on physics motivation; it goes straight to defining the recursion x_{n+1}. This shows that JSTAT accepts a math-first introduction when the problem sits in an established stat-mech line of work (resetting).
   - **Packaging.** No theorem environments. Section titles like "A remarkable asymptotic equivalence" and "A key scaling result" play the role of theorem labels. Appendices: "Some identities involving Stirling numbers", "Asymptotic behavior of the series".
   - **References.** Strongly mathematical: Spitzer (14 hits), Sparre Andersen (5), Feller (3), Flajolet (2).
   - **Figures.** Simulations up to n = 10^5 are compared with predicted slopes.
   - Source: [arXiv:2203.01102](https://arxiv.org/abs/2203.01102).

8. **Rossetto, "The one-dimensional asymmetric persistent random walk", J. Stat. Mech. (2018) 043204.** DOI 10.1088/1742-5468/aab507. 18-20 pp, 9 figure files in 3 figure environments. This is the most directly relevant model, a persistent random walk.
   - **Abstract.** 204 words. Physical framing first ("Persistent random walks are intermediate transport processes between a uniform rectilinear motion and a Brownian motion ... governed by the telegrapher's equation ... designed to resolve the paradox of the infinite speed in the heat and diffusion equations"), then "We derive exact expression of its Green's function, for its scattering statistics and distribution of first-passage time at the origin."
   - **Introduction.** Causality and the heat equation (Cattaneo, Vernotte, Thomson's transatlantic cable). The conclusion names a physical application: "This case is physically relevant in, for instance, microtubule growth."
   - **Packaging.** No theorem environments. Appendices on function properties and transforms. Cites Goldstein (3 hits) and Abramowitz-Stegun.
   - **Corrections.** The arXiv v3 carries a footnote that typos in the published version were pointed out by Giona et al., a reminder that JSTAT referees do not always check derivations exhaustively.
   - Source: [arXiv:1712.06447](https://arxiv.org/abs/1712.06447).

9. **Gastner, "The Ising chain constrained to an even or odd number of positive spins", J. Stat. Mech. (2015) P03004.** DOI 10.1088/1742-5468/2015/03/P03004. 19 pp, 7 figures. This is a finite-size 1D Ising chain paper with a magnetization-distribution section.
   - **Abstract.** 116 words: "We calculate the partition function using a generalization of the transfer matrix method. On this basis, we derive the exact magnetization ... By taking the thermodynamic limit together with the limit of zero temperature and zero magnetic field, the constraints lead to new scaling functions and different probability distributions for the magnetization. We demonstrate how these results solve a stochastic version of the one-dimensional voter model."
   - **Introduction.** The Ising model as a "cornerstone" with applications from solid state to neuroscience to social phenomena. Section 2 is titled "Motivation: Stochastic synchronous voter model", so the physical or applied model is given as the motivation before any computation.
   - **Packaging.** No theorem environments; 82 eqnarrays. The section "The probability distribution of the magnetization" explicitly "repeat[s] here the arguments developed by Antal et al." (domain-wall counting Ω(d,M)), using **periodic** boundary conditions.
   - **Keywords.** Commented-out keyword lines in the source read "Rigorous results in statistical mechanics, solvable lattice models" and "Ising chain, voter model, exact results". These look like candidate JSTAT taxonomy keywords, but I could not see the final published set.
   - Source: [arXiv:1502.02883](https://arxiv.org/abs/1502.02883).

10. **Godrèche and Luck, "New insights into the distribution of the topmost gap in random walks and Lévy flights", J. Stat. Mech. (2025) 073207.** DOI 10.1088/1742-5468/adec65. 22 pp, 4 figures.
    - **Abstract.** Very short (50 words): "Building upon the knowledge of the distribution of the first positive position reached by a random walker starting from the origin, one can derive new results on the statistics of the gap between the largest and second-largest positions of the walk, and recover known ones in a more direct manner."
    - **Keywords (arXiv source).** "Random walks, Lévy flights, Ladder variables, Wiener-Hopf method". The source uses the Springer `sn-jnl` class, which suggests the manuscript was prepared for or submitted to a Springer journal before appearing in JSTAT (inference).
    - **Introduction.** Positions the work almost entirely within the probability literature (Pollaczek, Wendel, Sparre Andersen, Spitzer, Baxter, Feller; Schehr-Majumdar 2012; Pitman). Physics applications appear only in one list sentence.
    - **References.** Ann. Probab. (2 hits), J. Appl. Probab. (1), Spitzer (15).
    - **Packaging.** No theorem environments. The key idea is stated as a displayed equation Z = min(H1, H2) with an explanatory figure.
    - Source: [arXiv:2502.18391](https://arxiv.org/abs/2502.18391).

**Family B: mathematical-physics hybrid**

11. **Artuso, Cristadoro, Onofri, Radice, "Non-homogeneous persistent random walks and averaged environment for the Lévy-Lorentz gas", J. Stat. Mech. (2018) 083209.** DOI 10.1088/1742-5468/aad822. 11 pp, 3 figures.
    - **Abstract.** Two sentences, 63 words.
    - **Author keywords.** "Persistent random walks, Lévy-Lorentz gas, Anomalous transport".
    - **Introduction.** Starts from Fürth and Taylor's lattice persistent walk ("a probability ... of jumping in the same direction and a probability ... of reversing the direction of motion"), which is almost exactly the author's Galton-board model. Applications cited: polymers, chemotaxis, active matter.
    - **Packaging.** Uses Tauberian theorems (Feller) and polylog asymptotics (Flajolet), and comments on what is and is not "rigorously proven" in the literature, all without theorem environments.
    - Source: [arXiv:1805.09889](https://arxiv.org/abs/1805.09889).

**Family C: Theorem/Proof format in JSTAT**

12. **Coletti, Gava, Schütz, "A strong invariance principle for the elephant random walk", J. Stat. Mech. (2017) 123207.** 7 pp, 0 figures.
    - **Abstract.** "We prove a strong invariance principle for the ERW ... As a by-product of our result we get the law of iterated logarithm and the central limit theorem."
    - **Structure.** "Introduction and results" / "Proof of Theorem X". It defines theorem, lemma, corollary, proposition, definition and remark environments.
    - **Introduction.** Brief model-history motivation with no physical applications.
    - Source: [arXiv:1707.06905](https://arxiv.org/abs/1707.06905).

13. **Coletti, de Lima, Gava, "Limit theorems for a minimal random walk model", J. Stat. Mech. (2019) 083206.** DOI 10.1088/1742-5468/ab3343. 13 pp, 0 figures.
    - **Structure.** Introduction / Definition of the model / Main results / Proofs (Preliminaries, martingale lemmas, SLLN, CLT, LIL). 8 theorem and 4 proof environments.
    - **Abstract.** "We prove the law of large numbers ... Then we prove the central limit theorem and the law of the iterated logarithm ...".
    - Source: [arXiv:1908.09199](https://arxiv.org/abs/1908.09199).

14. **Mailler and Uribe Bravo, "Random walks with preferential relocations and fading memory: a study through random recursive trees", J. Stat. Mech. (2019) 093206, 49 pp.** 39-page arXiv PDF, 7 figures.
    - **Abstract.** It explicitly bridges to physics: "This process has been analyzed in the physics literature under the name random walk with preferential relocations, where it is argued that ... We prove rigorously the central limit theorem described above".
    - **Packaging.** Full theorem apparatus (6 theorems, 4 propositions, 4 lemmas, 8 proofs, conjecture environment). Proof sections plus a "Main steps of the proofs and heuristics" section. Cites J. Appl. Probab. and Bernoulli.
    - Source: [arXiv:1810.02735](https://arxiv.org/abs/1810.02735).

**Other search leads**
- Hartich and Godec, J. Stat. Mech. (2019) 024002, DOI 10.1088/1742-5468/ab00df, "Interlacing relaxation and first-passage phenomena in reversible discrete and continuous space Markovian dynamics". Per the search result, its keywords are "exact results, stochastic processes, stochastic search, fluctuation phenomena", and its abstract says the duality is "derived and proven rigorously". I could not open the PDF (password-protected), so its structure is unverified. Source: [search result / MPG PDF](https://www.em.mpg.de/634361/Hartich_2019_J-Stat-Mech.pdf).
- Antal, Droz, Rácz, "Probability distribution of magnetization in the one-dimensional Ising model: effects of boundary conditions" is **J. Phys. A 37 (2004) 1465, not JSTAT**. It computes finite-size magnetization distributions for periodic, antiperiodic, free and block boundary conditions, and it is the natural citation for the author's Ising-chain equivalence. Source: [arXiv:cond-mat/0308442](https://arxiv.org/abs/cond-mat/0308442).

### Inferences
- The default JSTAT format for exact results on RTPs and persistent walks is:
  - an abstract of about 130-200 words, written in "We consider / We find / We show" voice, usually ending with "We verify ... through numerical simulations";
  - an introduction that opens with physics (active matter, bacteria, telegrapher's equation and causality, Ising or voter models);
  - an early "model and summary of main results" section;
  - derivations in the main text and lengthy computations in appendices;
  - figures that overlay exact curves on simulation data.
- For the author's paper, the closest templates are:
  - **Mallmin-Blythe-Evans 2019**: lattice PRW, exact spectral solution, no simulations needed.
  - **Rossetto 2018**: 1D persistent RW, telegrapher framing, Green's functions and first passage.
  - **Godrèche-Luck 2022/2025**: discrete-time walks, heavy use of the classical probability literature, exact asymptotics with correction terms, short math-first introduction.
  - **Gastner 2015**: finite Ising chain, magnetization distribution, transfer matrix, applied motivation via the voter model.

### Gaps
- Official JSTAT keyword sets for most of these papers could not be read because iopscience blocked automated access. The keywords reported above are author-supplied or commented-out keywords from the arXiv sources, or come from a search snippet (Hartich-Godec). The author should check each article page by hand.
- Typeset JSTAT page counts were not obtained; the counts above are arXiv-version pages.
- I did not find a JSTAT paper whose main subject is the finite-size magnetization distribution of the free-boundary zero-field Ising chain. The key reference (Antal-Droz-Rácz 2004) is in J. Phys. A.
- I did not find a JSTAT paper by Angelani or Orsingher on telegraph processes in the time available. Angelani's 1D RTP first-passage paper, arXiv:1506.08046, appeared in EPJ E, per the search.

---

## Q2. Are there JSTAT papers using Theorem/Proof format, and how common is it?

### Takeaway
Yes. JSTAT publishes fully theorem-proof papers on random walks (Coletti et al. 2017 and 2019; Mailler-Uribe Bravo 2019), but they are a clear minority. None of the 11 physics-community exact-results papers sampled (including every Majumdar/Schehr/Mori/Dhar/Kundu/Godrèche-Luck/Evans paper) defines a single theorem environment. Theorem-style JSTAT papers tend to come from probabilists. They state "we prove" in the abstract, have no figures or simulations, and offer little physical motivation beyond naming the model's physics origin.

### Cited Findings
- arXiv `jr:"Stat. Mech" AND abs:"we prove" AND abs:"random walk"` returned only 5 papers in total, including Coletti et al. 2019, Mailler-Uribe Bravo 2019 and Coletti et al. 2017. "we prove" + "Ising" returned 4, mostly quantum or Cayley-tree models. This suggests proof-language abstracts are rare among JSTAT random-walk papers. — [arXiv API search](https://export.arxiv.org/api/query?search_query=jr:%22Stat.+Mech%22+AND+abs:%22we+prove%22+AND+abs:%22random+walk%22)
- Parsed LaTeX counts of theorem environments:
  - 0 in each of 1711.08474, 1906.09442, 1810.00813, 2107.00338, 1412.7381, 1912.08778, 2203.01102, 1712.06447, 1502.02883, 1805.09889 and 2502.18391;
  - 8 theorems, 2 lemmas and 4 proofs in 1908.09199;
  - 1 theorem, 2 corollaries and 1 proof in 1707.06905;
  - 6 theorems, 4 propositions, 4 lemmas and 8 proofs in 1810.02735.
  - Sources: [1908.09199](https://arxiv.org/abs/1908.09199), [1707.06905](https://arxiv.org/abs/1707.06905), [1810.02735](https://arxiv.org/abs/1810.02735).
- The physics-style papers use "proof" only informally, as appendix titles. Singh-Kundu has "Proof of the identity"; Godrèche-Luck 2022 has "Alternative derivation of some of the results". — [1906.09442](https://arxiv.org/abs/1906.09442), [2203.01102](https://arxiv.org/abs/2203.01102)
- Mailler-Uribe Bravo show a bridging strategy: name the physics literature's heuristic claim, then "prove rigorously" it and extend it, and include a "Main steps of the proofs and heuristics" section. — [1810.02735](https://arxiv.org/abs/1810.02735)
- The search snippet for Hartich-Godec 2019 says results were "derived and proven rigorously" and the paper carries the keyword "exact results". JSTAT's taxonomy also includes "Rigorous results in statistical mechanics", which appears as a candidate keyword in Gastner's source. — [Hartich-Godec](https://www.em.mpg.de/634361/Hartich_2019_J-Stat-Mech.pdf), [1502.02883](https://arxiv.org/abs/1502.02883)

### Inferences
- A hybrid is safest for the author:
  - state the main results as a small number of numbered theorems or propositions, which is acceptable to JSTAT (Family C precedent);
  - surround them with physics-style framing: a "Model and main results" section, physical motivation (Ising chain, persistent walkers, RTPs), and figures comparing exact law, Bessel bounds and asymptotics;
  - move long proofs, such as the uniform Bessel bounds and the remainder R_N estimate, to appendices, as Families A and B do.
- A pure theorem-proof paper with no figures is publishable in JSTAT, but it would read like Coletti et al. Those papers succeed partly because their models (elephant RW, minimal RW) already have a physics literature. The author should likewise put the PRW/RTP/Ising literature up front.

### Gaps
- No systematic count over all JSTAT papers was possible. The "minority" claim rests on this sample plus the narrow arXiv keyword searches.

---

## Q3. How do Majumdar, Schehr, Le Doussal, Mori, Dhar, Sabhapandit, Kundu, Evans, Godrèche-Luck and similar authors present exact results in JSTAT?

### Takeaway
Results are announced in prose ("we show", "we find", "we derive exact expressions"), often summarized in an early "model and main results" section with the key formulas displayed. Asymptotic or scaling forms are emphasized, along with universality or comparison with the Brownian case. Every key formula is checked against simulations, either in figures or in captions saying "numerical verification", and technical steps go to numerous appendices. The mathematical literature (Feller, Spitzer, Sparre Andersen, Lamperti, Kac, Orsingher) is cited as background or for classical identities, not as a framework for theorem-proving.

### Cited Findings
- Mori-Gradenigo-Majumdar: the "We show" phrase appears 9 times and "we find" 30 times, with 9 appendices. Section 2 is "The model and the summary of the main results". The abstract ends with "Our results are supported by numerical simulations performed with a constrained Markov chain Monte Carlo algorithm." — [2107.00338](https://arxiv.org/abs/2107.00338)
- Malakar et al. (Dhar, Majumdar, Sabhapandit, Kundu, Redner): 4 appendices, 8 figures. The captions compare exact formulas with "explicit Langevin simulations ... 10^6 different realizations". — [1711.08474](https://arxiv.org/abs/1711.08474)
- Godrèche-Majumdar-Schehr: the abstract states conditions in prose ("if ρ(τ) admits a well defined first moment, i.e., if it decays faster than 1/τ^2") rather than as a formal hypothesis list. The introduction credits Lamperti's earlier probabilistic analysis and positions the paper as "a complete and thorough re-examination". — [1412.7381](https://arxiv.org/abs/1412.7381)
- Godrèche-Luck: section headings act as result labels ("A remarkable asymptotic equivalence", "A key scaling result"). Exact solutions for specific step distributions are clearly separated from "heuristic analysis of other distributions". Spitzer and Sparre Andersen are cited heavily. — [2203.01102](https://arxiv.org/abs/2203.01102), [2502.18391](https://arxiv.org/abs/2502.18391)
- Hartmann-Majumdar-Schawe-Schehr: exact means plus numerical full distributions down to 10^-100 via MCMC. The abstract openly states which results are exact and which are numerical. — [1912.08778](https://arxiv.org/abs/1912.08778)
- Mallmin-Blythe-Evans: exact results without simulation. The figures visualize the exact spectrum, and the abstract ends with a broader physical-relevance claim (exceptional points). — [1810.00813](https://arxiv.org/abs/1810.00813)

### Inferences
- These authors' "exact" means a closed-form or explicitly computable result derived with physicist's rigour, such as Laplace transforms and Bromwich inversions. Their papers therefore make no distinction between proof and derivation. The author's paper, which contains genuine uniform bounds and an error term R_N, can claim a stronger standard of rigour. It should still present the results the way these papers do: the formula first, then its meaning (where the crossover occurs, its scaling with log N), then a numerical comparison.
- The crossing equation z_N + (1/2) log z_N = log N + ... fits the Majumdar/Schehr "explicit asymptotics with first correction" style well. A figure plotting exact p*_N against the asymptotic solution, with and without the 1/(8 z_N) correction, would match genre expectations (inference).

### Gaps
- No Le Doussal-authored JSTAT paper on RTPs or persistent walks was verified in this session. Basu and Angelani JSTAT papers were also not verified.

---

## Q4. JSTAT papers on the 1D Ising chain magnetization distribution at finite size, or on persistent random walks on lattices

### Takeaway
On lattice persistent walks, JSTAT has Rossetto 2018 (the 1D asymmetric PRW), Artuso et al. 2018 (a lattice PRW with transmission and reflection probabilities, Fürth-Taylor style) and Mallmin-Blythe-Evans 2019 (lattice RTPs). On the finite Ising chain, JSTAT has Gastner 2015 (periodic chain, constrained, with a magnetization-distribution section built on Antal et al.). The canonical free-boundary magnetization-distribution paper (Antal-Droz-Rácz 2004) is in J. Phys. A. I found no JSTAT paper connecting a persistent walk to a free-boundary Ising chain magnetization, which suggests the author's equivalence could be presented as a selling point (inference).

### Cited Findings
- Rossetto 2018, JSTAT 043204: "The isotropic and symmetric one-dimensional persistent random walk is governed by the telegrapher's equation ... We derive exact expression of its Green's function, for its scattering statistics and distribution of first-passage time at the origin." — [1712.06447](https://arxiv.org/abs/1712.06447)
- Artuso et al. 2018, JSTAT 083209, introduction: "random walkers with nearest neighbour jumps, where the walker has a probability ... of jumping in the same direction and a probability ... of reversing the direction of motion". — [1805.09889](https://arxiv.org/abs/1805.09889)
- Mallmin et al. 2019: "An RTP is more generally an example of a persistent random walker (PRW)", modelled on a ring lattice with hardcore exclusion. — [1810.00813](https://arxiv.org/abs/1810.00813)
- Gastner 2015, JSTAT P03004: the magnetization-distribution section explicitly reuses Antal et al.'s domain-wall counting for **periodic** chains. — [1502.02883](https://arxiv.org/abs/1502.02883)
- Antal, Droz, Rácz 2004, J. Phys. A 37, 1465: finite-size magnetization distributions for periodic, antiperiodic, free and block boundary conditions; the block distribution is identical to free. — [arXiv:cond-mat/0308442](https://arxiv.org/abs/cond-mat/0308442), [ResearchGate](https://www.researchgate.net/publication/1938111_Probability_distribution_of_magnetization_in_the_one-dimensional_Ising_model_Effects_of_boundary_conditions)
- Other JSTAT persistent-walk paper found: "Jamming of multiple persistent random walkers in arbitrary spatial dimension", J. Stat. Mech. (2020) 103207, 18 pp, 10 figures. I did not analyze its structure. — [arXiv:2006.01590](https://arxiv.org/abs/2006.01590)

### Inferences
- The author should cite Antal-Droz-Rácz for the free-boundary Ising magnetization law and Rossetto, Artuso et al. and Mallmin et al. as JSTAT precedents for lattice PRWs. This signals to editors that the topic sits within JSTAT's scope.

### Gaps
- There may be JSTAT papers on discrete-time persistent walks (the Galton-board type) that I did not find, because arXiv full-text search is limited.

---

## Q5. Synthesis: shared patterns of accepted mathematical-style JSTAT papers, and differences from a probability journal (e.g. J. Appl. Probab.)

### Takeaway
Accepted JSTAT papers in this area share six features:
- a physically motivated opening;
- a "model + main results" section near the start;
- results stated as displayed formulas in "we show/derive" prose, or occasionally as theorems;
- long derivations in appendices;
- numerous figures comparing exact results with simulation or numerics;
- long bibliographies (30-67 references) dominated by physics, with selective classical probability citations.

Typical length is 20-36 arXiv pages, with outliers from 7 to 49. Compared with a probability journal, the emphasis shifts from completeness of proof and hypotheses to physical meaning, scaling and universality, and visual and numerical confirmation.

### Cited Findings
- **Length (arXiv pages).**
  - Physics-style papers: 1711.08474 = 26; 1906.09442 = 32; 1810.00813 = 29 (31-page PDF); 2107.00338 = 24; 1412.7381 = 30; 1912.08778 = 21; 2203.01102 = 36; 1712.06447 = 18-20; 1502.02883 = 19; 2502.18391 = 22; 1805.09889 = 11.
  - Theorem-style papers: 1707.06905 = 7; 1908.09199 = 13; 1810.02735 = 49 pp in the journal reference.
  - Sources: arXiv comment fields and PDF page counts for each ID above, e.g. [1906.09442](https://arxiv.org/abs/1906.09442), [1810.02735](https://arxiv.org/abs/1810.02735).
- **Figures.** Physics-style papers: 3-11 figure environments, nearly all including simulation overlays (1711, 1906, 2107, 1912, 2203). Theorem-style papers: 0 figures (1707, 1908); the exception, 1810.02735, has 7 illustrative figures. — same sources
- **Bibliography size.** Physics-style: 30-67 entries (57, 49, 46, 65, 39, 67, 38, 31, 30, 31, 38). Theorem-style: 13-18 for Coletti et al.; 44 for Mailler-Uribe Bravo. — same sources
- **Abstracts.** Physics-style abstracts run 116-302 words, typically "We consider/study ... We find/show/derive exact ... We verify ... numerical simulations." Godrèche-Luck 2025 (50 words) and Artuso et al. (63) show that very short abstracts are also accepted. — [2107.00338](https://arxiv.org/abs/2107.00338), [2502.18391](https://arxiv.org/abs/2502.18391), [1805.09889](https://arxiv.org/abs/1805.09889)
- **Introductions.** Physical openings include active matter and bacteria (1711, 2107, 1912), Einstein-Smoluchowski and detailed balance (1810), causality of the heat equation and the telegrapher's equation (1712), the Ising model as a cornerstone with social and neuro applications (1502), and the arcsine laws with finance and disordered-systems applications (1906). — sources above

### Inferences
**Differences from a probability-journal paper (J. Appl. Probab., Ann. Appl. Probab.)** (inference from the sample plus general knowledge of those journals, not separately sourced)
- **Opening.** JSTAT papers lead with a physical system and why an exact solution matters (non-equilibrium, active matter, finite-size effects). A probability paper leads with the stochastic model and its relation to prior theorems.
- **Statement of results.** JSTAT presents displayed formulas with interpretation (scaling, universality, comparison with Brownian or Ising behaviour). Probability journals expect numbered theorems with full hypotheses.
- **Rigour.** In JSTAT, the derivation is the "proof", and approximations are labelled "heuristic" rather than avoided. Rigour beyond that is welcome but not required, and it is not the main selling point.
- **Numerics.** Simulations or exact-enumeration overlays are expected in JSTAT, and abstracts routinely state "verified numerically". Probability journals rarely require them.
- **Citations.** JSTAT bibliographies are physics-heavy: Majumdar-Schehr reviews, active-matter reviews and Weiss's book for PRWs. Feller, Spitzer, Kac and Orsingher appear as classical anchors.
- **Keywords.** JSTAT uses a controlled taxonomy (for example "exact results", "stochastic processes", "rigorous results in statistical mechanics", "solvable lattice models", "first passage", "extreme value statistics", "active matter"). Gastner's source and the Hartich-Godec snippet give partial evidence for this.

**Concrete recipe for the author's resubmission** (inference)
1. Title and abstract in "We consider ... We obtain the exact law ... We derive explicit uniform Bessel-function bounds ... We locate the switching probability ... whose asymptotics are given by ... Exact enumeration confirms ..." form, about 150 words.
2. An introduction that opens with persistent walkers and RTPs (active matter), the telegrapher's equation and the zero-field Ising chain with free boundaries. The Galton board serves as the intuitive picture.
3. A "Model and summary of main results" section stating 3-4 results, either as displayed equations or as Theorem 1-3, each followed by a physical reading.
4. Main-text derivations at Malakar/Mori depth, with the uniform-bound proofs and the R_N estimate in appendices.
5. 4-8 figures: the exact law versus N; bound tightness per bin; p* versus N against the crossing-equation asymptotics, with and without correction terms.
6. Cite JSTAT precedents (Rossetto 2018, Artuso et al. 2018, Mallmin et al. 2019, Malakar et al. 2018, Gastner 2015, Godrèche-Luck 2022/2025), Antal-Droz-Rácz 2004, and classical probability sources (Feller, Orsingher, Kac).
7. Keywords drawn from JSTAT's taxonomy, e.g. "exact results", "stochastic processes", "rigorous results in statistical mechanics", "solvable lattice models". These need to be verified against the current JSTAT keyword list.

### Gaps
- The official JSTAT keyword taxonomy page and author guidelines were not retrieved, because iopscience blocked access. The author should consult the JSTAT "author guidelines" and keyword list directly.
- The contrast with J. Appl. Probab. is based on general knowledge plus the JSTAT sample. No J. Appl. Probab. papers were analysed in this session.
