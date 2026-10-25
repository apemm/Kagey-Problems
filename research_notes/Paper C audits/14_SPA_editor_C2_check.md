# Paper C audit 14. Editor's check of Paper C2 for SPA

October 24, 2026. Manuscript `kagey-problems/problem131/paperC2/problem131_reconstruction.tex`
(elsarticle, SPA), read in full in order, against the referee report (audit 10), the split record
(audit 12), `paperC/EXPORTS.md`, the C1 PDF `paperC/problem131_chains.pdf` (build of October 24)
and the proof records `C theorems 5 and 7/02_T5_class_uniform.md` and `04_T7_cycle_tree.md`.

## Decision

Send to referees. The mathematics is in good order. Every referee item that falls in C2 is fixed
correctly, both main theorems survived the move intact, and the imports match C1. The check found
four small defects in the imports and one gap in the statement of a lemma, all fixed below. After
the line edit the paper has 40 pages, within the 30 to 40 of the guide.

## Referee items

| Item | Where now | Verified |
|---|---|---|
| Precise `def:controlled` | Def 4.3, with Lemma 4.2 and the remark after it | Yes. Omega = (0, inf) x R^d is named. S_Q is open and dense with closed nowhere dense complement (finite union of tie sets, each with empty interior by the tau-slope or the strict v_j-monotonicity of lambda_F). W_Q is locally constant and shift invariant. The equivalences in the remark (agreement off a closed nowhere dense set, open set of disagreement, agreement on the killing quadrant) are correct. No threshold is in the definition. Thresholds are in Lemmas 4.4 and 4.5 with their dependence. |
| Exposure induction step by step | Lemma 4.4, Lemma 4.5, Prop 4.6 | Yes, with one fix. Lemma 4.4: the Collatz and Wielandt test vector, epsilon = eta x_*/(2 q_max) and the bound on bar v_0 check line by line. Lemma 4.5: the generic-partner argument (v = t e_j), the margins delta, kappa, the identity Phi(H) - Phi(F) = (lambda_H - lambda_F)(tau - rho_H), and the removal of outside faces (gap 1/2) all check. The proof enlarges bar v_0 beyond the threshold of Lemma 4.4, while Lemma 4.4 as stated only gave lambda_G >= its own threshold. The proof of Lemma 4.4 works for every larger threshold, so the lemma now says so. Prop 4.6: irreducibility of Q' (open set where V wins meets dense S_Q'), the singleton slab (pair at least 1/2 above the better singleton since tau q_max <= 1/2), and the face step (density of S_Q' in O, continuity of the scores, tie on the hypersurface, Lemma 3.2 to extend, c = 0 from lambda_V(0) = 0) all check against Def 4.3. |
| `thm:nonreversible`(d) restricted | Thm 3.5(c) and the paragraph after it | Yes. (c) is stated for an irreducible Z-matrix with the principal minors of -Q, and the uniqueness of the generator point is step (N), which uses exactly that the spectrum is that of Q. The counterexample 3I - P is right (eigenvalues 3 - spec P, none zero). |
| v = 0 excluded in (f) | Prop 3.8(b) | Yes. The exceptional set is closed and nowhere dense and contains v = 0, where r = 1, l = pi and a_V(0) = mu(V) = 1 for every generator. |
| Irreducibility of Q' (survival) | Remark 3.4 | Yes. A reducible Q' has lambda'_V = lambda'_C on an open set for a component C != V, independent of v_j for j not in C, against d lambda_V/d v_j = -alpha*_j < 0. Lemma 3.2 then applies on all of R^d. |
| Identifiability induction as a proposition | Prop 4.6 | Yes. Both forms are stated and the equivalence is the remark after Def 4.3. |
| Intro fiber sentence with no-cut condition | Section 1.2, "What is borrowed and what is new" | Yes. Loewy (and Hartfiel and Loewy for order at most 3) with the no-cut condition, Al Ahmadieh's converse, the CGGR orbit of cut-transposes. The Al Ahmadieh pointer now names Theorem 4.1 and Lemma 4.5. |
| Data-first borrowed-and-new paragraph | Section 1.2 | Yes. It starts with the data, names the exposure lemma as the main contribution and the translation to generators as the shortest step. |
| Notation collisions | Sections 3 to 5 | Yes for the items the referee named (d, delta, tau, D, h). Remaining reuses are listed under problems not fixed. |
| Tie remark | after Thm 6.2 | Yes. It no longer claims that lower-order terms always break ties, and gives the symmetric case. |
| Uniformization bound | proof of Lemma 6.9 | Yes. Rates between states of [d] at most 1 (after the rescaling when gamma < 0), into the cemetery at most max(c, epsilon), so exit rates at most d - 1 + max(c, 1) and varkappa > d + c works, including V_ij = 0 and gamma = 0. Holding probabilities stay bounded below, so the rare-transition limits hold. |
| N_0 sentence after Thm 5.7 | after Thm 5.7 | Corrected. "The admissible range of N grows like b^-2" was imprecise. It now says the least admissible N, of order U R log N, grows like b^-2, which is what `03_T5_numerics.md` item 7 reports. The claim about the dip near N of order bar v T matches item 9 there. |

## Imports from C1

Each statement of Section 2 was compared with the C1 PDF.

| C2 | C1 | Finding |
|---|---|---|
| Lemma 2.1 | Lemma 2.2(b), (c), Thm 4.2(ii) | C2 letters the parts differently from C1, and part (c) is the last line of C1 Thm 4.2(ii). The pointer now gives the parts. |
| Lemma 2.2 | Lemma 3.2 | Matches. |
| Prop 2.3 | Props 3.1 and 3.4 | (c) lacked the irreducibility of F that C1 assumes. Added. The derivative in (b) is not in C1's statement but is justified in the sentence after it. |
| Lemma 2.4 | Lemma 4.1 and (6) | Matches (C uniform over compact field sets since theta(v) stays in a compact subset of V_F). |
| (2.2) | (1) | Matches. |
| Thm 2.5 | Thm 4.2 and Rem 4.3 | (c) was stated for every start and every field. C1 gives it for every start only at v = 0 (Thm 4.2(iii)) and for a field only under a full-support start (Rem 4.3). The hypothesis is restored. Every use in C2 (Section 6, v = 0) is covered. |
| Def 2.6, Prop 2.7 | Def 5.1 and the text after it, Prop 5.2 | Match. |
| Thm 2.8, Thm 2.9 | Thms 5.7, 5.6 | Match. |
| Prop 5.6 | Prop 5.16 | Matches, including the class, the starts, the fields and the constants. |

C1's Theorems 4.4 and 5.8 and Lemma 2.3 are mentioned in C2 only for comparison, as an open
question and for a script. No proof uses them. Remark 5.8 used Lemma 2.4 with a constant uniform
in the start, which the imported statement does not give. It now uses linearity of the law in the
start and Lemma 2.4 for the two point starts, which is correct.

Leftover search over all `.tex`, `.md` and `.py` files in `paperC2` for Bessel, boundary layer,
complete graph, near-vertex, crossing, window of tied faces, forest, weak field, Hypothesis L,
layer, appendix and old section numbers. The only hits are the crossing equation of C1 (cited as
an open question) and the crossing equation solved inside `verify_finite_horizon.py`, both
intended. Every label quoted in a script docstring exists in the paper.

## The two main theorems

Theorem 5.7 (finite horizon) against `02_T5_class_uniform.md`, Theorem U6. Read in full. The
suppression step, the exact singleton switch with its expansion 2R log(mu_1/mu_i)/L + O(L/N),
the function Lambda_N(T) = -L + T/t + (1/2) log T + kappa + E, the window of width C_5 U/L, the
solution for T° and the constant c_ij, and part (c) through Thm 5.5 all agree with the record.
The record's Lemma U5 survives as the suppression paragraph with the gap 3/4, and Prop U4 is the
imported Prop 5.6. Nothing was lost.

Theorems 6.11 and 6.12 (cycle tree) against `04_T7_cycle_tree.md`, Theorems 7.7 and 7.10 and
Lemmas 7.5, 7.6, 7.9. Read in full. Part (a) keeps the case gamma > D(G), which is all the
statement needs. Part (b) keeps the four cases (disjoint, inside, containing, mixed with Lemma
6.9 and laminarity). The paper drops "noncritical" from the heights, which is correct since no
case uses it. Lemma 6.9 adds killing at rate epsilon off K so that all rates of the enlarged
chain are positive, a harmless strengthening. Lemma 6.10 and Theorem 6.12 match. Nothing was
lost.

Theorems D to G of the introduction match Theorems 3.3, 3.5 with the example after it, Prop 3.7,
Thm 4.7 with Prop 4.6, Thms 5.2, 5.3, 5.5, 5.7 with Remark 5.8, and Thms 6.11, 6.12.

## Framing

- Retention. Abstract ("retains the same information"), Section 1.2 ("We should say plainly"),
  and now Section 4.1, which says in one sentence that the result is read as retention.
- Theorem G is in the abstract and has its own paragraph in Section 1.4.
- Al Ahmadieh. Section 3 cites Lemma 5.1 of arXiv:2309.00806v2 (version in the bibliography).
  The introduction now says "Lemma 5.1" as well.

## Format

The guide for authors was read again on October 24, 2026 from
https://www.sciencedirect.com/journal/stochastic-processes-and-their-applications/publish/guide-for-authors.

| Requirement | Status |
|---|---|
| elsarticle `preprint,12pt` | yes |
| Title page with corresponding author clearly indicated, full postal address | Fixed. Added `\corref` and `\cortext` and the street address (301 Platt Boulevard). |
| Abstract at most 250 words | 249 by a whitespace count |
| References in the abstract | The guide says avoid them, cite author and year if essential, and its reference section says references cited in the abstract must be given in full. The one reference now carries journal, volume, year and article number. |
| 1 to 7 keywords | 7 |
| MSC | not mentioned in the guide, 2020 codes given with `\MSC[2020]` |
| Funding sentence | the guide's standard sentence, present |
| Competing interests | through the declarations tool, and the section in the manuscript agrees |
| Acknowledgements directly before the references | yes |
| Numbered references, alphabetical | yes, 25 entries |
| Key steps outlined before details | Sections 3 and 4 open with an outline and the introduction sketches Theorems D and E. Added a two-line outline of the proof of Theorem G at the head of Section 6 and one sentence before the proof of Theorem 5.7. |
| Length 30 to 40 pages | 40 (was 41) |

## Line edit

Pages saved: 1 (41 to 40), with about 14 lines free on page 40. No result, proof or example was
removed. Cuts were to repeated prose: the opening of Section 6 (which restated Section 1.4 and
the related work), the opening of Section 6.2, the discussion after Prop 6.7, the paragraph after
Thm 6.11, the summary after Thm 6.12 (now one sentence pointing to Theorem G), the pointer to
Section 7 at the end of Section 6, the literature paragraph after Lemma 3.2, the first paragraph
of Section 7 and the sentence in Section 4.1 that repeated Section 1.2.

## Candidate cuts of proved material (for the author, not made)

| Candidate | Estimate |
|---|---|
| Theorem 6.13 (prefactors from window endpoints) with the discussion after it | 1.2 pages |
| Proposition 3.8 (amplitudes) with its proof and the paragraph after it | 0.9 page |
| Example 6.6 (branch switch) with its proof | 0.4 page |
| Remark 5.4 (partial data) | 0.4 page (script docstring to update) |
| The four-state cut-transpose example after Thm 3.5 | 0.3 page (script docstring to update) |
| Proposition 3.7 (stationary start) | 0.3 page (it is Theorem D(iii)) |
| Remark 3.6 (three states by hand) | 0.2 page |
| Remark 5.9 (size of the correction) | 0.2 page |
| Remark 6.14 (what the design needs) | 0.2 page |

## Edits made

- `problem131_reconstruction.tex` 44 to 48: `\corref`, `\cortext`, `addressline`.
- `problem131_reconstruction.tex` 56 to 60: abstract, "coarse" removed, "answering", full
  reference.
- `sec_intro.tex` 59: "Lemma 5.1 of Al Ahmadieh". 120: "[Theorem 4.1 and Lemma 4.5]".
- `sec_prelim.tex` 60: pointer of Lemma 2.1 to C1 Lemma 2.2(b), (c) and Thm 4.2(ii). 87: "If F
  is irreducible" in Prop 2.3(c). 119: hypothesis "v = 0, or mu of full support" in Thm 2.5(c).
- `sec_minors.tex` 76 to 82: literature paragraph after Lemma 3.2 shortened.
- `sec_modal.tex` 22: retention sentence. 119: "Every larger value of bar v_0 also serves" in
  Lemma 4.4, and 147 the matching clause in its proof. 280: the open set where V wins added to
  the list of strict regions used.
- `sec_reversible.tex` 333 to 337: N_0 sentence corrected and a one-sentence outline of the proof
  of Thm 5.7. 402 to 404: Remark 5.8 now uses linearity in the start.
- `sec_lowtemp.tex` 3 to 13: opening shortened, outline of the proof of Theorem G added. 375,
  391, 425, 433, 620, 664: concision edits. The last paragraph of Section 6 removed.
- `sec_verify.tex` 3 to 6: first paragraph shortened.
- `cover_letter.md`: length paragraph replaced by "40 pages, within the usual 30 to 40".
- `README.md`: page count 40. `TEMPLATE.md`: date of the second reading of the guide, the
  abstract reference rule, the corresponding-author mark, the address, 249 words, 40 pages.

## Problems not fixed

- Notation still reused across sections: G is the graph in Section 5 and a face in Section 4,
  Delta_ij in Thm 5.2 against the simplices Delta_F, c and K carry several meanings in Section 5,
  and tau_+ means different things in the exposure proof and the singleton step of Prop 4.6. None
  collides inside one statement.
- Lemma 4.5 proof: "tau_- > delta" needs U chosen with closure inside the region where
  tau_1 > 2 delta. One phrase would fix it. Left for the author since it touches a proof.
- Thm 2.5 is stated uniformly for tau in a compact interval, while C1 states it at fixed tau. The
  C1 proof gives the uniformity, and C2 uses it only pointwise.
- The claim after Thm 5.7 about exact three-state computations rests on
  `C theorems 5 and 7/03_T5_numerics.md`, not on a script in `paperC2`.
- The bibliography gives the short title of C1. EXPORTS.md has the subtitle.
- The cover letter still has the placeholder for the arXiv number.

## Build and scripts

Built three times in `paperC2`: 40 pages, no undefined references, no multiply defined labels,
no overfull or underfull boxes, no warnings. `py -I verify_all.py`: 4 of 4 PASS (173 s). The
auxiliary files and the `__pycache__` folder the run created were deleted, and the PDF was kept.
