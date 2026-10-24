# Paper C audit 05: trimming plan for the JTP version

Date: October 24, 2026. Scope: `kagey-problems/problem131/paperC/problem131_chains.tex` and every
file it inputs, as built on October 24 (94 pages, `problem131_chains.log`). No manuscript file was
edited. Line references are `file:line` in the current sources. Statement numbers are those of
the current build (`problem131_chains.aux`). The README of the folder still uses the numbers of
the EJP build of October 23, so I cite `\label` keys next to numbers.

Constraints taken as fixed. The paper gets shorter. Proofs stay in the article, in appendices
where they are long (JTP keeps proofs in the paper, not in an Online Resource). The near-vertex
section stays as the worked case of the boundary layer. The controlled-boundary model must stop
looking contrived. The text must say what is Good's, what is Kim and Landim's, what is the
principal-minor literature's, and what is new, and Theorem 4 (Theorem `thm:nonreversible`) must be
argued as the translation to generators plus the exposure lemma.

Two facts drive the plan more than any single cut.

1. **The supplement no longer counts as a proof location.** `supplement.tex` is archived, and
   proofs must be in the article. Four statements of the current draft are proved only there:
   Proposition 5.15 `prop:nextterm` and Lemma B.2 `lem:laplace2` (supplement S3 and S4, see
   `sec_secondorder.tex:812-821`, `app_laplace.tex:141-142` and `155-158`), Proposition 5.14
   `prop:threecycle` (S2, `sec_secondorder.tex:764`), and the rows $P_d$ and $\Theta_\varepsilon$ of
   Table 2 (S1, `sec_examples.tex:205-214`). Bringing them in costs about 12 pages
   (supplement lines 493-1029). So each of them is either cut from the article or demoted to a
   statement that the article proves in a few lines. This is not optional, and it is also the
   largest single saving.
2. **The draft proves several things twice.** The killed functional is developed twice
   (Proposition 4.1 `prop:rate` in `sec_firstorder.tex:164-344` and Section 3 `sec_dv.tex`), the
   face maxima with a field are proved three times (Proposition 5.16 `prop:weakfield`(b),
   Proposition 9.1 `prop:controlled-score`, Proposition 9.13 `prop:uniform-facemax`), and the
   4-cycle is worked out twice (Section 4.1 `sec:worked` and Corollary 8.1 `cor:C4`). Proving each
   once, in its general form, saves about 9 pages without losing a statement.

Target: about 62 pages including appendices and bibliography, from 94, with the new boundary-layer
section (about 4 pages of text plus 2.5 of appendix) and the cycle tree (about 2 pages) added.

---

## 1. Inventory of the current build

Pages are read off the table of contents and the label pages in `problem131_chains.aux` (start page
of each unit; a unit that starts and ends on the same page is counted by its share of lines). Figures
and tables are counted where LaTeX placed them. The page counts are estimates to about 0.3 page.

| Unit | Source lines | Pages (approx.) | Role |
|---|---|---|---|
| Front matter, abstract | `problem131_chains.tex:59-80` | 0.5 | front (abstract not written) |
| **1 Introduction** | `sec_intro.tex` | **5.3** | |
| 1.1 Face selection, Thm A, Fig. 1 | 12-69 | 1.3 | headline statement, figure |
| 1.2 Second order, Thms B, C | 71-169 | 2.0 | headline statements |
| 1.3 Related work | 171-276 | 1.8 | remark (literature) |
| 1.4 Plan | 278-308 | 0.4 | remark (outdated, still mentions the supplement and no Parts III, IV) |
| **2 Setting, notation, exact law** | `sec_model.tex` | **4.6** | |
| 2.1 Notation, Def 2.1, two-state walk recall | 7-111 | 1.7 | supporting (lines 96-104 recall Paper A) |
| 2.2 Lemma 2.2 admissible faces | 113-160 | 0.6 | supporting lemma |
| 2.3 Lemma 2.3 runs, Lemma 2.4 continuum | 162-270 | 1.5 | supporting lemma (Good's formulas) |
| Example 2.5 four models, Fig. 2 simplex | 272-321 | 0.8 | example, figure |
| **3 Killed functional, spectral geometry** | `sec_dv.tex` | **3.4** | |
| 3.1 Prop 3.1 restriction identity | 13-54 | 0.7 | core (the reading), 2-line proof |
| 3.2 Prop 3.2 variational formula | 56-162 | 1.6 | supporting (duplicates Prop 4.1(a),(b),(c)) |
| Lemma 3.3 face monotonicity | 164-205 | 0.6 | supporting (classical, cited twice elsewhere) |
| Thm 3.4 stratified local law | 207-232 | 0.5 | headline (proof is one line of citations) |
| **4 First-order face selection** | `sec_firstorder.tex` | **8.0** | |
| 4.1 Worked 4-cycle, Table 1, Fig. 3 | 7-162 | 2.5 | example (heuristic, "we do not give proofs", line 24) |
| 4.2 Prop 4.1 rate on a face | 164-344 | 2.6 | supporting (duplicated by Section 3) |
| 4.3 Lemma 4.2 upper bound, Thm 4.3 | 346-475 | 1.9 | core |
| 4.4 Thm 4.4 hull, Fig. 4 cycles | 477-598 | 1.9 | core plus figure |
| **5 Second-order theory** | `sec_secondorder.tex` | **14.0** | |
| 5.1 Def 5.1 tilt, Prop 5.2 constant, Cor 5.3 | 17-174 | 2.7 | core |
| 5.2 Thm 5.4 local law, Lemma 5.5, Thm 5.6 face maxima | 176-321 | 2.2 | core |
| 5.3 Thm 5.7 crossing, Thm 5.8 tie windows | 323-510 | 2.3 | core |
| 5.4 Prop 5.9 forest, Lemma 5.10 Cayley, Ex 5.11, Rem 5.12 flows | 513-705 | 2.7 | supporting / remark |
| 5.5 Rem 5.13, Prop 5.14 directed 3-cycle | 707-765 | 1.0 | example (full proof only in supplement S2) |
| 5.6 Prop 5.15 next term | 768-843 | 1.2 | supporting (proof only in supplement S3, S4) |
| 5.7 Prop 5.16 weak field | 846-947 | 1.9 | supporting (third proof of field face maxima) |
| **6 Two-state walk and complete graph** | `sec_complete.tex` | **7.0** | |
| 6.1 Prop 6.1 pair identity, Cor 6.2 two-state walk | 8-61 | 1.0 | supporting / verification against Paper A |
| 6.2 Cor 6.3, (6.x) interior law, Thm 6.4, Thm 6.5, Cor 6.6, Rem 6.7 | 63-228 | 2.4 | core (Theorem C) |
| 6.3 A start: Cor 6.8, Rem 6.9, Cor 6.10, Rem 6.11, Ex 6.12, Rem 6.13 | 230-370 | 2.0 | examples, one unproved heuristic (Rem 6.13) |
| 6.4 Weak field: Cor 6.14, Ex 6.15, Cor 6.16 | 372-499 | 1.6 | examples (feed Fig. 1(b)) |
| **7 Near a vertex** | `sec_vertex.tex` | **1.2** | worked case (stays) |
| **8 The 4-cycle and other graphs** | `sec_examples.tex` | **3.6** | |
| Cor 8.1 4-cycle cascade, $c_F$ values, $N=10^{14}$ test | 11-120 | 2.0 | example (repeats 4.1), verification |
| Table 2, Rem 8.2 outcomes | 122-227 | 1.6 | example table (rows proved in Lean or supplement only) |
| **9 Reconstruction** | `sec_reconstruction.tex` | **17.0** | |
| 9.1 Observation model, Prop 9.1 controlled score | 22-136 | 1.3 | core (re-proves Thm 4.3 with a field) |
| 9.2 Lemma 9.2, Thm 9.3 reversible, Thm 9.4 minimality, Thm 9.5 stability | 138-465 | 4.5 | core (9.3), supporting (9.4, 9.5) |
| 9.3 Lemmas 9.6-9.9, Rem 9.10, Thm 9.11, Cor 9.12 | 467-1002 | 7.0 | core (Theorem 4 and the DV corollary) |
| 9.4 Prop 9.13, Thm 9.14, Rem 9.15, Rem 9.16 | 1004-1300 | 4.2 | core (Theorem 5), constant tracking |
| **10 Low temperature** | `sec_lowtemp.tex` | **6.8** | |
| 10.1 Thm 10.1 depth, Thm 10.2, Prop 10.3, Thm 10.4, Ex 10.5, Ex 10.6 | 28-458 | 6.5 | core (10.2, 10.4), supporting (10.1, 10.3), examples |
| 10.2 Cycle tree | 460-462 | 0.3 | placeholder (being written) |
| **11 Verification, open questions; declarations** | `sec_verify.tex`, main 104-124 | **2.3** | verification |
| **App. A local law and first-order bounds** | `app_torus.tex` | **9.0** | |
| A.1 Lemma A.1 Perron root, proof of Prop 5.2(a) | 19-128 | 1.5 | proof |
| A.2 Lemma A.2 torus representation | 130-224 | 1.3 | proof (Good's resolvent formula) |
| A.3 proof of Lemma 4.2 | 226-286 | 0.8 | proof |
| A.4 proof of Thm 5.4 | 287-400 | 1.8 | proof |
| A.5 proof of Lemma 5.5 | 401-485 | 1.2 | proof |
| A.6 proof of Thm 4.3(ii) | 486-587 | 1.3 | proof (reducible faces) |
| A.7 Lemma A.3 forest formula | 589-700 | 2.0 | proof (only for Prop 5.9) |
| **App. B Laplace lemma, next term** | `app_laplace.tex` | **2.0** | proof; B.1-B.2 point to the supplement |
| **App. C complete graph** | `app_complete.tex` | **3.0** | proof |
| **App. D near a vertex** | `app_vertex.tex` | **1.8** | proof |
| **Bibliography (50 items)** | `bib_switching.tex` | **4.5** | |
| Table 2 float on the last page | | 0.8 | (counted above) |

---

## 2. Ranked cut list

Ranked by pages saved per unit of referee risk. "Moves to" says where any statement that is still
needed goes. "arXiv only" means the arXiv version keeps the material as an extra appendix, which
the journal version omits (the arXiv version can be longer than the journal version, as for D).
Removed proofs go into `removed_proofs/` as before, so they can come back in a revision.

### Tier 1: consistency and duplication (do all of these)

**C1. Statements whose only proof is in the archived supplement.** Saves 3.5 pages.

- *The next term*, Prop 5.15 `prop:nextterm` (`sec_secondorder.tex:768-843`), Lemma B.2 and
  B.1-B.2 (`app_laplace.tex:110-158`). Lost: the term $c_F/T$ in the local law, in $\log M_F$ and in
  the crossing equation, the values $c_F=-1/(8q_{ij})$ and $-(k-1)/8$, the $1/(8T)$ term of
  Theorem C(i) and of Cor 6.2, and the computer-algebra values $c_{\rm arc3}$, $c_{C_4}$
  (`sec_examples.tex:91-120`). Moves to: arXiv only (supplement S3, S4 become an arXiv appendix).
  In the article, Thm 6.4(ii)-(iii) `thm:simplex-crossing` is stated with error $O(1/L)$ in the
  crossing equation, and one remark says that the next term $1/(8T)$ is that of Paper A for $k=2$
  and of the Bessel majorant of Paper B v1 (Theorem 6.2 there) for $k\ge2$, which
  `sec_complete.tex:171` already notes. Eq. (5.x) `eq:simplex-root-expansion` loses its last term.
  Risk: low. The $1/(8T)$ term is not a headline for JTP, and both earlier sources prove it.
  Knock-on: the Paper A recall `sec_model.tex:96-104` ($z_N$, $c_0$, the Bessel bound
  `eq:planar-bessel`) is then used only by Cor 6.2 and can shrink to two lines.
- *The directed 3-cycle*, Prop 5.14 `prop:threecycle` (`sec_secondorder.tex:722-765`) with
  Rem 5.13 `rem:half` (712-720). Lost: part (iv), the identification of the global modes on all
  ranges, which is the long part of S2. Moves to: an Example in the second-order section with
  parts (i)-(iii) only, each proved in the text in a few lines (the exact $M_{\{1\}}$, $M_{\{1,2\}}$,
  the root equation of (ii), and (iii) from Thm 5.6). Remark 5.13 merges into it. About 0.6 page
  instead of 1.0. Risk: moderate if deleted (a referee asks whether (H) is needed), low as an
  example. Keep it.
- *Table 2 and Remark 8.2* (`sec_examples.tex:122-227`). Rows $P_d$, $\Theta_\varepsilon$ rest on
  the supplement, and rows $C_d$, paw, house, $K_4$ plus a vertex are "Lean only". JTP referees will
  not accept a Lean-only row as proved, and "proved in the supplement" no longer applies. Lost: the
  table and the community picture. Moves to: arXiv only (with supplement S1). The article keeps one
  remark after the hull theorem with the two rows that the text proves in a few lines, namely $K_d$
  (all faces tie at $\tau=1$) and the symmetric-$Q$ row ("with unit rates on a connected graph the
  winners go from the vertices straight to $[d]$ exactly when the graph is complete",
  `sec_examples.tex:181-194`), and one sentence on disjoint communities. About 0.5 page. Risk: low.

**C2. One development of the killed functional.** Saves 2.5 pages.

Prop 4.1 `prop:rate` (`sec_firstorder.tex:164-344`) and Section 3 (`sec_dv.tex:13-205`) prove the
same facts. Part (d) of Prop 4.1 (lines 299-305) is the restriction identity
(`sec_dv.tex:31-48`) on a subface. Part (a) is Prop 3.2 `prop:variational` at $v=0$, and the proof
of Prop 3.2 says that it "follows" the proof of Prop 4.1 with a shifted diagonal (`sec_dv.tex:99-101`).
The reversible form appears in both (Prop 4.1(c) and the end of Prop 3.2). The strict decrease of
the Perron root under passage to a principal submatrix is cited at `sec_firstorder.tex:306-309`,
proved in Lemma 3.3 (`sec_dv.tex:179-205`), and cited again at `sec_secondorder.tex:937-939`.

Plan: one section, "The killed functional", that defines $J_V$ and $J_F$ (and never $I_F$: rename
throughout, which removes `sec_dv.tex:22-25`), and proves, with a field $v$ from the start: the
restriction identity; the variational formula $\lambda_F(v)=\min(J_F-v\cdot\alpha)$ with the
unique interior minimizer; strict convexity and attainment (old Prop 4.1(b)); the reversible form
(old Prop 4.1(c) and the end of Prop 3.2, written once); Legendre duality. Lemma 3.3 becomes one
sentence with the citation to Berman and Plemmons (their result for $0\le B\le A$, $B\ne A$, $A$
irreducible, covers reducible principal submatrices padded with zeros, which is the only reason
the draft gives a proof, `sec_dv.tex:174-177`), plus the two-line consequence about $\gamma(v)$. The
worked numbers on the pair (`sec_firstorder.tex:181-184`) go. Risk: none; nothing is lost.

**C3. State the face maxima with a field once, and derive the three field results from it.**
Saves 3.5 pages.

The field enters every estimate only as the diagonal shift $Q_F\mapsto Q_F+\operatorname{diag}v_F$
(`sec_reconstruction.tex:24-28`), and Lemma 4.2 `lem:upper` with the Perron tilt
$\theta=q-v-\lambda_F(v)\ones$ handles it (lines 71-86). The objects of Def 5.1 do not see the
diagonal (lines 1041-1046). So:

- State Lemma 4.2, Thm 4.3(ii)-(iii) and Thm 5.6 `thm:facemax` for the weighted law
  $P_N(n)e^{Tv\cdot n/N}$ with $v$ in a compact set, with $\lambda_F(v)$, $\alpha^*_F(v)$ and
  $K_F(v)$. The proofs change by one line each. Then Prop 9.1 `prop:controlled-score`
  (`sec_reconstruction.tex:45-136`, 1.3 pages) becomes a three-line corollary (the reducible-face
  block argument, lines 108-121, repeats `app_torus.tex:513-534`).
- The weak field is the same law at $v=\xi/T$: $T\lambda_F(\xi/T)=T\lambda_F-\langle\xi,\alpha^*_F\rangle
  +O(1/T)$ by the variational formula, and $K_F(\xi/T)=K_F+O(1/T)$. So Prop 5.16(b)-(c)
  `prop:weakfield` (`sec_secondorder.tex:869-879`, proofs 899-932) is a four-line corollary of the
  field face maxima, provided they are stated uniformly for $v$ in a compact neighbourhood of $0$,
  which Prop 9.13 already proves. Part (a) is one sentence. Part (d) (lines 880-882, 934-946) is not
  used anywhere; cut it.
- Prop 9.13 `prop:uniform-facemax` (`sec_reconstruction.tex:1023-1149`) is mostly a walk through
  the constants of four proofs (items (i)-(v), lines 1090-1148). If Lemma B.1 (already stated over
  a compact metric space, `app_laplace.tex:10-11`) and the proofs in Appendix A are written once
  with a compact parameter set $\mathcal P$ of $(Q,\mu,v)$, Prop 9.13 is a statement plus half a
  page, and its constant tracking moves into Appendix A as one paragraph per lemma.

Risk: low. Nothing is lost, and the "uniform on the class" statement becomes visibly a theorem of
Part I, which helps Theorem 5.

**C4. One 4-cycle.** Saves 3 pages.

Section 4.1 `sec:worked` (`sec_firstorder.tex:7-162`, 2.5 pages, heuristic, no proofs) and Cor 8.1
`cor:C4` (`sec_examples.tex:11-89`) cover the same faces; Cor 8.1(a) repeats 4.1, and Cor 8.1(c)
repeats Prop 6.1. Plan: one Example placed after Thm 4.4 `thm:hull`, with the exit rates, the
winners, the constants $K_F$ of Cor 8.1(b), and the two window kinks of Cor 8.1(e), proved by
citing Cor 5.3, Prop 5.2(b) and Thm 5.8. The motivating paragraph "stay versus share"
(`sec_firstorder.tex:20-27`, 143-156) goes into the introduction as three sentences. Table 1
merges into Fig. 3 (the figure already has both pictures; the table repeats the exponents). Cut:
the 3-arc test at $N=10^{14}$ (`sec_examples.tex:108-120`, keep one sentence that the explicit form of
Thm 5.7(iii) is off by 0.06 there, as in `sec_secondorder.tex:380-383`), and the $c_F$ values (C1).
Fig. 4 `fig:cycles`: keep panel (b) only (the finite-$N$ mode on $C_5$ supports the "approached
slowly" caveat); panel (a) illustrates the same theorem as Fig. 3(b). Risk: low.

**C5. Introduction, related work, plan.** Saves 2.8 pages. The introduction must be rewritten
anyway: it does not mention Parts III and IV, and the plan (`sec_intro.tex:278-308`) still sends the
reader to the supplement. Target 2.5 pages: one paragraph of setting, the five headline theorems
in short form, one paragraph "what is earlier and what is new" (Section 4 below), and a one-paragraph
plan. Related work (`sec_intro.tex:171-272`, 1.8 pages) shrinks to about 0.8 page; the long accounts
of Edwards, Wang and Yang, Kassan-Ogly and Filippov (lines 219-239) become one sentence each, and
the sentence "Their paper was not accessible to us" (237-238) goes.

**C6. Verification section and scattered Lean remarks.** Saves 1.5 pages. `sec_verify.tex` (2 pages)
becomes one paragraph plus the data-availability statement. The open questions shrink to five lines
and move to the end of the introduction or the last section. The Lean sentences are scattered
(`sec_model.tex:198`, `sec_firstorder.tex:341-342`, 572-577, `sec_complete.tex:38-40`, 110, 227,
349, 498, `sec_examples.tex:87-89`, 197-205); collect them in the verification paragraph. The
paragraph on Paper B's scripts (`sec_verify.tex:37-49`) goes to the README.

### Tier 2: judgment cuts (needed to reach about 62 pages)

**C7. The tree formula for a general face.** Saves 3.5 pages. Prop 5.9 `prop:forest`
(`sec_secondorder.tex:513-627`) and Lemma A.3 `lem:forest` (`app_torus.tex:589-700`) give $K_F$ on a
non-reversible face through two tree counts and $\prod_\rho(\rho-\lambda_F)$. No headline result
uses them: Theorem 4(f) uses Prop 5.2(a) (`sec_reconstruction.tex:909-910`), and the complete graph
uses Cor 5.3 and Lemma 5.10. Lost: a pleasant closed form, and the directed-cycle constant of
part (d), which only cross-checks the 3-cycle. Moves to: arXiv only, with one sentence after
Prop 5.2. Rem 5.12 `rem:flows` (`sec_secondorder.tex:674-705`) becomes three sentences in the
related-work paragraph on Bertini, Faggionato and Gabrielli and on Kim and Landim (Lemma 5.7), since
that is where it serves; its inequality $R_F\ge I_F$ is used once (`sec_firstorder.tex:344`). Keep
Lemma 5.10 (Cayley) and Ex 5.11 (complete face), which the complete graph needs. Risk:
low to moderate. A referee interested in non-reversible chains might want the closed form, but
Prop 5.2(a) already gives $K_F$ for every irreducible face through $\det\nabla^2J_F$.

**C8. "A start" on the complete graph.** Saves 1.5 pages. Section 6.3 (`sec_complete.tex:230-370`).
Keep Cor 6.10 `cor:start-modes` (the lines $\ell^\mu_k$) and Ex 6.12 `ex:K3-start` (the window of
width $\log(16/(9\sqrt3))$, which uses only Thms 5.6, 5.8 and exact balancing). Fold Cor 6.8 into
Cor 6.10 (it is Thm 5.7 with $K_F=\mu(F)D_k/k$). Rem 6.11 (order of the winners) becomes one
sentence, since the same two-inequality argument is Thm 4.4(b). Rem 6.9 (balancing can fail)
becomes one sentence. Rem 6.13 `rem:K3-finite` (lines 353-370) is a heuristic that the text says it
does not prove: arXiv only. Risk: low.

**C9. The weak field on the complete graph.** Saves 0.8 page (or 2.5 with the full cut).
Section 6.4 (`sec_complete.tex:372-499`). After C3 the general weak field is a corollary, so this
section only illustrates it. Recommended: keep Cor 6.14 `cor:weakfield-phases` and Cor 6.16
`cor:weakfield-full-hierarchy`, which produce Fig. 1(b) and the one memorable statement ("one field
lets every support size win in turn"); cut Ex 6.15 (it is Step 4 of the proof of Cor 6.14 with
$d=3$) and the closing paragraph 441-446. Full cut (alternative): drop the section and panel (b) of
Fig. 1, which then shows only the single jump; saves 2.5 pages; risk moderate, because the
introduction loses its picture of intermediate faces winning. I recommend keeping the two
corollaries.

**C10. Reconstruction compressions.** Saves 3 pages in total.

- Thm 9.4 `thm:minimality` (`sec_reconstruction.tex:298-383`, 1.4 pages). Keep part (a) as a short
  proposition (the chart is Wolfer and Watanabe's, lines 375-379, and the rank argument is classical),
  proof cut to the chart and two sentences. Part (b) (fibers of partial data) becomes one sentence.
  Part (c) (the three-state family) stays as a two-line remark, since it is the cleanest reason
  why the boundaries of a spanning tree are not enough. Saves 0.8. Risk: low to moderate; a referee
  asking "why $m+d-1$ boundaries" is answered by (a).
- Thm 9.5 `thm:stability` (lines 385-465, 1.3 pages). The text itself calls it "a conditioning
  application of standard perturbation bounds" (463-465). Keep the statement and the two constants
  $h_*$ and $g_*$, which are the only new content; replace the arithmetic (lines 407-423, 442-460) by
  Weyl's inequality and the Davis and Kahan bound in four sentences. Theorem 9.14(c) still applies.
  Saves 0.7. Risk: low.
- Thm 9.11(e) `thm:nonreversible` ($d=3$). Audit 01 (S1) found that it is Hartfiel and Loewy (1984,
  Theorem 3) plus the normalization (N). Cite it and keep the cycle-product proof
  (lines 873-900) as a three-line remark, or drop it. Saves 0.5.
- Rem 9.10 `rem:singleton-partner` (lines 714-725): cut; the lemma does not need it. Rem 9.16
  `rem:finite-size` (1284-1299): two sentences. Saves 0.5.
- Lemma 9.6 `lem:RF-irreducible` and Lemma 9.7 `lem:perron-branch` (lines 488-570, 1.6 pages).
  The decision of October 24 says that C proves its own irreducibility and Perron-branch lemmas,
  so neither proof is cut. A shorter route for Lemma 9.7 exists: once $R'_F$ and $\widetilde R$
  share an open piece of a smooth hypersurface (the image $\phi(U)$, whose regularity is the
  inverse-function step at lines 553-561), the real Nullstellensatz for an irreducible polynomial
  with a regular real zero (Bochnak, Coste and Roy, Theorem 4.5.1) gives $\widetilde R\mid R'_F$
  at once. That replaces the elimination of $w_1$ (lines 548-566) by four lines but adds a citation
  for a step that is now elementary and self-contained. Saves 0.3. My recommendation is to keep the
  elementary proof and only tighten its wording. Citing Al Ahmadieh (Lemma 5.1, Cor. 5.6) for
  Lemma 9.6 instead of proving it would save 0.6, but goes against the decision.

**C11. Low temperature.** Saves 1.4 pages. In Thm 10.1 `thm:depth` the reversible cut bound and
the exponent formula (`sec_lowtemp.tex:88-93`, proof 151-194) are a second proof of a special case of
the Catoni route; Part IV never uses $\mathfrak h_F$ again. Cut them to arXiv only, or keep the
statement as a two-line remark without proof. Ex 10.6 `ex:branch-switch` (426-458) shrinks to its
statement and three lines. Keep Prop 10.3, Thm 10.4 and Ex 10.5 (the noncycle window is the
obstruction that Theorem 7 must face).

**C12. Small items.** Saves 2.5 pages in total.

- Cor 6.2 `cor:paperA` (`sec_complete.tex:42-61`): a consistency check with Paper A; becomes a
  two-line remark after Prop 6.1. 0.4.
- Rem 6.7 `ex:simplex-edge-mode` (216-228) and Rem 7.3 `rem:B-boundary` (`sec_vertex.tex:77-85`):
  one sentence each (the second quotes results of Paper B v1 that are not used). 0.6.
- Example 2.5(iii) sticky hidden Markov model and (iv) planar walk (`sec_model.tex:288-297`): (iii)
  is not used; (iv) is used only to introduce the 4-cycle. 0.3.
- Lemma 2.4 `lem:continuum` proof (`sec_model.tex:227-270`, 0.9 page): the density is Good's
  formula (10) with killing retained. Keep a proof (it is short and checks the killing and the
  $m_i-1$ exponents), but cut it to half a page. 0.4.
- Appendix A.3 (proof of Lemma 4.2, `app_torus.tex:226-286`): Good's coefficient identity and the
  triangle inequality give the bound with the constant $2^k\sup|B_\mu|$ and without the factor
  $e^{C_\theta T^2/N}$ (note `research_notes/Occupation novelty and compact advances/12_Good_original_closure.md`,
  Section 2B). Appendix A.5 (proof of Lemma 5.5): the lower bound by one word, already used at
  `sec_reconstruction.tex:1115-1126`, replaces the appeal to the local law. 0.8.

### Assessed and kept

- **The exact balancing theorems**, Thm 6.5 `thm:simplex-balance` with App. C.2 (about 1.1 pages in
  total). They give Theorem C(ii) at every $N$, make Cor 6.6 a statement about balanced compositions
  rather than supports, and are used in Ex 6.12. This paper replaces Paper B on arXiv, so a cut would
  leave the theorem only in B v1. Cost of keeping is small. Keep. If pages are short at the end, the
  fallback is to state Cor 6.6 for supports and cite B v1 for balancing (saves 1.1, risk moderate).
- **The reducible-face lower bound** in App. A.6 (`app_torus.tex:536-587`). Theorem A holds "for
  every start", and with a start that is not of full support a reducible face can win (the directed
  3-cycle). Keep.
- **The near-vertex section** (instruction), repositioned as the worked case of the boundary layer.

### Summary of savings

| Item | Pages saved |
|---|---|
| C1 supplement-only statements | 3.5 |
| C2 one killed functional | 2.5 |
| C3 field-first face maxima | 3.5 |
| C4 one 4-cycle | 3.0 |
| C5 introduction | 2.8 |
| C6 verification, Lean remarks | 1.5 |
| Tier 1 total | 16.8 |
| C7 general tree formula | 3.5 |
| C8 a start | 1.5 |
| C9 weak field on $K_d$ (recommended form) | 0.8 |
| C10 reconstruction | 3.0 |
| C11 low temperature | 1.4 |
| C12 small items | 2.5 |
| Tier 2 total | 12.7 |
| **All cuts** | **29.5** |
| New: boundary layer (text 4, appendix 2.5), cycle tree (2), new references (0.7) | +9.2 |
| **Net** | 94 - 29.5 + 9.2 = **73.7** |

The net from cutting alone is about 74 pages, because the current pages also hide some slack (float
placement, long proofs written at a slow pace). The spine in Section 3 budgets each section from
scratch at 63 pages. The difference has to come from a line edit of the proofs that are kept
(Appendix A, Theorem 4's proof, Thm 10.1), which in my experience with B and D gives 10 to 15
percent. If the line edit falls short, the next cuts, in order, are: the full weak-field cut (C9
alternative, 1.7 more), exact balancing to B v1 (1.1), Prop 9.13 in the class-uniform form only for
the reversible class (0.8), and the Catoni proof of Thm 10.1 shortened to a citation plus the
exit-time bounds (0.7).

---

## 3. The spine (about 63 pages with appendices)

### Headline theorems

- **Theorem A (the stratified local law).** For a face $F$ with (H), uniformly on compact parts of
  the open face and for $1\le T\le N^{1/3}$,
  $-\log P_N(n)=(k-1)L+TJ_V(n/N)-\frac{k-1}2\log T-\log C_F(n/N)+O(1/T+T^2/N)$, where $J_V$ is the
  Donsker and Varadhan functional of the whole chain, by the restriction identity. With a field,
  the face maxima $M_F(T,v)=K_F(v)N^{-(k-1)}T^{(k-1)/2}e^{-T\lambda_F(v)}(1+O(1/T+T^2/N))$, uniformly
  for $(Q,\mu,v)$ in compact sets. This merges Thm 3.4, Thm 5.4, Lemma 5.5, Thm 5.6 and Prop 9.13(b).
- **Theorem B (the boundary layer).** The Bessel layer between a face and a facet (from
  `research_notes/C theorems 5 and 7/08_T2_boundary_layer.md`), with the near-vertex law of the
  complete graph (Thm 7.2 `thm:vertex-uniform-root`) as its worked case in the lattice regime
  $T\asymp\sqrt N$. State only what is proved without Lemma L, or prove Lemma L; the note proves
  the pair case and the rate expansion unconditionally and the general case under Lemma L.
- **Theorem C (modal supports and crossings).** First-order selection with a field (Thm 4.3(ii)-(iii)
  plus Prop 9.1), the hull (Thm 4.4), the crossing equation (Thm 5.7) and the tie windows (Thm 5.8).
  The complete graph (Thms 6.4, 6.5, Cor 6.6, with start and weak field) is its worked case.
- **Theorem D (reconstruction).** In the reframed form of Section 5 below: the modal-support map of
  the killed chains and the Donsker and Varadhan functional carry the same information, namely the
  principal minors of $-Q$ (Thm 9.11(a), Cor 9.12); the generator fiber (Thm 9.11(b)-(d)); the
  amplitude obstruction (Thm 9.11(f)); the explicit reversible design with its minimal number of
  boundaries and its stability (Thms 9.3, 9.4(a), 9.5); finite horizons (Thm 9.14).
- **Theorem E (low temperature).** Noncritical selection by least-size deep cycles (Thm 10.2), the
  critical windows with the prefactor rule and the noncycle window (Thm 10.4, Ex 10.5), and the cycle
  tree read by the attraction design (Section 10.2, being written).

### Order and budget

| # | Section | Contents (current statement numbers) | Pages |
|---|---|---|---|
| | Front matter, abstract | | 0.7 |
| 1 | Introduction | Theorems A-E in short form, Fig. 1, earlier and new (Section 4 below), plan, open questions in five lines | 2.5 |
| 2 | Setting and the exact law | notation, Def 2.1, Lemma 2.2, Lemmas 2.3-2.4 credited to Good, Ex 2.5(i)-(ii), Fig. 2 | 2.5 |
| | **Part I. The law on a face** | | |
| 3 | The killed functional | $J_V$, $J_F$, restriction identity, variational formula with a field, monotonicity (cited), reversible form, Legendre duality (C2) | 3.0 |
| 4 | The stratified local law (Thm A) | Def 5.1, Prop 5.2 with Cor 5.3, Lemma 5.10, Ex 5.11; local law, discrete transfer, stratified display, face maxima with a field, uniform over compact parameter sets | 4.5 |
| 5 | The boundary layer (Thm B) | general layer theorem; the near-vertex law of $K_d$ as worked case (old Section 7, with $V_N$, $S_n$, $B_n$ defined locally) | 4.0 |
| | **Part II. Modal supports** | | |
| 6 | Face selection and crossings (Thm C) | Lemma 4.2 with a field, Thm 4.3, Thm 4.4, the 4-cycle example (C4), remark with the $K_d$ and symmetric-$Q$ rows (C1), Thm 5.7, Thm 5.8, the directed 3-cycle example (C1), weak field as a corollary (C3) | 6.0 |
| 7 | The complete graph | Prop 6.1, Cor 6.3, interior law, Thm 6.4 (error $O(1/L)$), Thm 6.5, Cor 6.6, starts (Cor 6.10, Ex 6.12), weak field (Cors 6.14, 6.16) | 4.0 |
| | **Part III. Reconstruction (Thm D)** | | |
| 8.1 | Coarse functionals of the law | the killed chain and its modal-support map; the controlled score law as a corollary of Section 6; statement of the equivalence with $J_V$ | 1.2 |
| 8.2 | The reversible case | Lemma 9.2, Thm 9.3, minimality (short), stability (short) | 3.0 |
| 8.3 | The non-reversible case | Lemmas 9.6-9.9, Thm 9.11 with the paragraph of Section 4 below, Cor 9.12 | 4.8 |
| 8.4 | Finite horizons | Prop 9.13 (statement), Thm 9.14, Rem 9.15 | 1.8 |
| | **Part IV. Low temperature (Thm E)** | | |
| 9 | Arrhenius families and the cycle tree | Thm 10.1 (Catoni route), Thm 10.2, Prop 10.3, Thm 10.4, Ex 10.5, Ex 10.6 short, cycle tree with the attraction design | 5.5 |
| 10 | Verification | one paragraph and availability statements; declarations | 1.0 |
| A | Proofs of the local law | Lemma A.1, Prop 5.2(a), Lemma A.2 (Good), Lemma 4.2, Thm 5.4, Lemma 5.5, Thm 4.3(ii), constants over $\mathcal P$ | 6.5 |
| B | Laplace lemma with a parameter | Lemma B.1 only | 1.5 |
| C | Proofs for the boundary layer and near a vertex | new layer proofs, old App. D | 4.0 |
| D | Proofs for the complete graph | old App. C | 2.5 |
| | Bibliography (about 60 items) | | 4.5 |
| | **Total** | | **63.5** |

Order note. The near-vertex law needs $S_n$, $V_N$ and $B_n$ from the complete graph. Defining them
at the start of the near-vertex subsection takes five lines (the definitions are
`sec_complete.tex:70-82` and `eq:refresh-polynomial` at 183-187), which keeps Part I together. The
alternative order (complete graph before the boundary layer) avoids the duplication but splits the
law on a face from its boundary.

---

## 4. Where the text must say what is whose

Each item gives the place in the current source, what must be said, and what is missing from the
bibliography.

### Good (1961)

Good 1961 (Ann. Math. Statist. 32, 41-48, DOI 10.1214/aoms/1177705137) is **not in
`bib_switching.tex`**; add it. His paper has no numbered theorems, so cite formula numbers
(the closure note 12 above lists them, Section 1).

1. Lemma 2.3 `lem:runs` (`sec_model.tex:174-196`): the exact law of the frequency counts with the
   exponents $n_r-1$ is Good's coefficient identity (3), p. 42, for a chain of $N$ letters with any
   initial law (his (1), p. 41). Whittle 1955 and Dawson and Good 1957 are already cited in the
   related work; say there that the run grouping is our way of writing Good's identity, and keep the
   proof (ten lines) for the killed version.
2. Lemma 2.4 `lem:continuum` (`sec_model.tex:211-225`): the interior density of the occupation times
   is Good's (10), p. 46, as a constant term. What we add is the killing (the subprobability with the
   full exit rates on the diagonal) and the check of the exponents $m_i-1$, where his p. 45 product
   prints $\tau_r/d\tau$ without the minus one (note 12, "A small but relevant prelimit discrepancy").
3. Lemma A.2 `lem:torus` (`app_torus.tex:145-220`): the resolvent generating function is Good's (2),
   and the torus integral is his constant-term formula. Say so in the sentence before the lemma.
4. Theorem 5.4 `thm:local` (`sec_secondorder.tex:181-205`): Good proposes saddle-point analysis of
   his formula and does not carry it out (pp. 42-43, "heavy"). Say that the local law, with its
   explicit constant, uniform relative error and discrete transfer, is the quantified completion of
   that suggestion, and that the relative cell transfer and the whole-face upper bound are short
   deductions from his identity (note 12, Sections 2B-2C). This is the honest form of the claim in
   "What is new" (`sec_intro.tex:47-55`), which today does not mention Good at all.
5. The two-state Bessel density (Good's (11), which he attributes to earlier work; Pedler 1971 for
   the two-state occupation law) belongs in the boundary-layer section, where the pair case of
   Theorem B is that formula written as a layer (note 08, Summary item 2). Pedler 1971 is not in the
   bibliography either.

What is not Good's, and the introduction should say it in one sentence: comparisons of maxima across
supports of different dimensions, the stratified display, the boundary layer, and everything in
Parts II-IV.

### Donsker and Varadhan, and the earlier rate literature

- Prop 3.2 `prop:variational` (`sec_dv.tex:86-90`): the finite form of the Donsker and Varadhan
  eigenvalue formula; already said, keep.
- The restriction identity (`sec_dv.tex:27-54`) has a two-line proof. Do not present the identity as
  a theorem of substance. What is new is the reading: every face rate is the restriction of one
  functional, so support competition is lattice entropy against Donsker and Varadhan cost, and that
  is what makes the corollary $J_V\leftrightarrow$ principal minors possible. Before the claim goes
  in, check Guillin, Nectoux and Wu (their conditional rate differs, as `sec_intro.tex:185-195`
  already notes) and Kim and Landim Section 5 for the identity in any form.

### Kim and Landim

Name these four places, each with the locator.

1. Their Lemma 5.1 ($J_V$ determines the exit rates and the products $w_{ij}$) and Corollary 5.3 (it
   determines a reversible generator): after Thm 9.3 (`sec_reconstruction.tex:290-296`) and after
   Cor 9.12 (995-1002). Say that the reversible reconstruction from $(q_i-q_1, w_{ij})$ is theirs in
   functional form, and that ours reads the same coordinates off modal boundaries with a design
   fixed in advance.
2. Their Example 5.4 (the uniform 3-cycle and its reversal share $J_V$): after Thm 9.11
   (lines 966-967) and after Cor 9.12. Their question, which generators share $J_V$, is the one that
   Cor 9.12 answers exactly; say this in the introduction.
3. Their Lemma 5.7 (the minimizing flow is $\alpha_iq_{ij}r_{\alpha,j}/r_{\alpha,i}$) and their
   (1.3)-(1.7) (the flow cost of Bertini, Faggionato and Gabrielli): where Rem 5.12 is compressed
   (C7), in the related work.
4. For $d=3$, Thm 9.11(e) is their Lemma 5.1 plus $\det(-Q)=0$, and also Hartfiel and Loewy (see
   below). The current remark (lines 964-967) gives only the first.

### Loewy, Hartfiel and Loewy, Engel and Schneider, Al Ahmadieh, and Chatterjee, Ghosh, Gurjar and Raj

`hartfielloewy1984` is **missing from the bibliography** (audit 01, S1); add it.

1. Lemma 9.6 `lem:RF-irreducible` (`sec_reconstruction.tex:526-529`): Al Ahmadieh, Lemma 5.1 and
   Corollary 5.6, over any field. Say that the lemma is a short version of hers for $-Q_F$.
2. Thm 9.11(c) (proof at 811-819): Loewy 1986, Theorem 1, for $d\ge4$ and no cut; Hartfiel and Loewy
   1984, Theorem 3, for $d\le3$. The theorem statement should say "$Q$ has no cut" (audit 01, M4).
3. Thm 9.11(d) (proof at 843-871): the orbit description is Chatterjee, Ghosh, Gurjar and Raj 2024,
   Theorem 1.1, with Definition 2.10 and Remark 2.11; that the fiber is one class exactly when there
   is no cut or the matrix is symmetrizable is Al Ahmadieh, Theorem 4.1 ($n\ge4$) and Lemma 4.5.
4. Reversible uniqueness (lines 864-871): Engel and Schneider 1980, Theorem 3.5, whose hypotheses
   audit 01 (S3) could not check; Al Ahmadieh, Lemma 6.1 and Theorem 6.2, which she says implies
   theirs; and the three-line argument of audit 01 (a symmetric matrix is its own cut-transpose),
   which needs no outside theorem. Use the three-line argument and cite both.
5. The remark after Thm 9.11 (lines 955-969) must then say, in this order: the matrix fiber is
   theirs; what is ours is listed in the next subsection.

### What is new, and where each claim is argued

| Claim | Where in the text | What the sentence must say |
|---|---|---|
| The restriction-identity reading | end of Section 3, intro | one functional for all faces; the stratified display; it makes Cor 9.12 possible (the identity itself is elementary) |
| The observation reduction | Section 8.1, before Thm 9.11 | the modal-support map of the killed chains determines $\lambda_F(v)$ on all of $\mathbb R^F$, for every irreducible face |
| The exposure lemma | Lemma 9.9 and the paragraph after it (lines 709-712) | this is the step that uses the boundaries of all faces, not only pairs; it is an algorithm; exposure by descent works for every face, the singleton form only for pairs and cycles |
| The generator normalization and the fiber | (N) in the proof of Thm 9.11 (776-788), and the remark after it | each orbit point has exactly one generator point; every member of the fiber is irreducible, has the spectrum of $Q$, and the fiber is finite; a reversible $Q$ is alone in it; a cut-transpose is a third generator on four states (print one with rational entries, audit 01, M5) |
| The amplitude obstruction | Thm 9.11(f) and the intro | from the stationary start the whole composition law of $Q$ and $Q^*$ agree for every $N$ and $T$; a generic start separates every fiber member through $K_V(v)$ |
| Critical windows | Thm 10.4, Ex 10.5 | at a critical depth the prefactors decide, and a noncycle wins on an open window of rescaled height of width $\log2$ |
| The attraction design | Section 10.2 (from note 04) | suppression masks depths; calibrated attraction $v=ct^\gamma$ on a face reads $D(F)=\max_{G\subseteq F}\tau(G)$ without knowing any rate |

**The argument for Theorem 4 (to be written as one paragraph after Thm 9.11 and in shorter form in
the introduction).** The principal-minor fiber of an irreducible matrix is known: Loewy and
Hartfiel and Loewy give it without a cut, Al Ahmadieh and Chatterjee, Ghosh, Gurjar and Raj describe
it across rank-one cuts. Three things separate that theorem from a statement about Markov chains.
First, the data. The principal minors are not observed; what the chain shows are occupation counts.
The exposure lemma and the Perron-branch lemma turn the boundaries of the modal-support map into the
functions $\lambda_F(v)$ for every face, and $\lambda_V(v)$ on an open set into all principal minors.
Second, the objects. A point of the matrix fiber is a matrix up to diagonal similarity and
transposition; the normalization (N) shows that each such point contains exactly one generator, that
every generator in the fiber is irreducible with the spectrum of $Q$, and that a reversible generator
is alone in its fiber. Third, the limit of the data. The amplitudes $K_F(v)$ separate the fiber for a
generic start, while from the stationary start no statistic of the counts can, which shows that the
time-reversal ambiguity belongs to occupation data and not to the observation model. Cor 9.12 then
answers Kim and Landim's question exactly: two generators share the Donsker and Varadhan functional
if and only if they share their principal minors.

---

## 5. Reframing the observation model

### What looks contrived now

`sec_reconstruction.tex:13-43` says "suppose that we can tilt the chain by a field and vary the time
scale, and that we observe only which face carries the mode". A referee reads this as an experiment
designed to make the theorem true. Three features cause it: the field looks arbitrary, the modal
support looks like a strange statistic, and the controlled boundaries appear before any reason to
care about them.

### Proposed frame: which coarse functionals of the occupation law determine the generator

Open Part III with the question: *which coarse functionals of the law of the occupation counts
determine the generator, and how much do they lose?* Then list three functionals, from fine to coarse.

1. The law of the counts at all $(N,T)$. It determines $Q$ from $N=2$, except that from the stationary
   start it cannot tell $Q$ from $Q^*$ (Thm 9.11(f), second claim, which is exact at every $N$).
2. The logarithmic scale of individual compositions, which by Theorem A is the Donsker and Varadhan
   functional $J_V$ (the stratified display reads $J_V$ off $-\log P_N(n)$ face by face).
3. The modal support of the killed chains, a finite label: the support of the most likely
   composition of the chain killed at known rates, conditioned to survive.

The main theorem of Part III is then that **2 and 3 carry the same information, namely the principal
minors of $-Q$** (Thm 9.11(a) with Cor 9.12), and that this information is $Q$ up to time reversal
without a cut and a finite generator fiber in general (Thm 9.11(b)-(d)). The controlled boundaries are
the way 3 is read, not a premise.

### Why the field is natural: it is a killing rate

Two facts already in the draft remove the arbitrariness.

- The weight $e^{Tv\cdot n/N}=\prod_te^{hv_{X_t}}$ is exactly the survival probability of a chain that
  is killed at each visit to $i$ with probability $1-e^{hv_i}$ when $v\le0$. So
  $P_N(n)e^{Tv\cdot n/N}$ is the probability of surviving with composition $n$, and the weighted
  mode is the mode of the counts conditioned on survival (the normalization does not move the mode).
  The killed matrix $Q_F+\operatorname{diag}v_F$ (`sec_reconstruction.tex:26-28`) is literally the
  killed generator with the extra killing.
- The shift $\lambda_F(v+c\ones)=\lambda_F(v)-c$ (`sec_dv.tex:64`) moves every score
  $\Phi_{\tau,v}(F)$ by the same $-\tau c$, so the winners depend on $v$ only up to constants, and
  every field can be taken $\le0$. **Every field in the paper is a killing profile.** The suppression
  fields are strong killing outside a face, and the exposure scan is a sweep of the observation
  horizon $\tau$ at fixed killing.

So the observation becomes: *for a chain with known extra killing rates, observed up to horizon
$T=\tau\log N$, which set of states does the most likely surviving trajectory occupy?* This is a
quasi-stationary question of a standard kind, and $\lambda_F(v)$ is the exit rate of $F$ for the
killed chain, which is the object the reader already knows from Part I.

### Why the modal support is a natural coarse functional

- By Theorem A, the support of the mode is the face that minimizes $|F|-1+\tau\lambda_F(v)$, that is,
  the outcome of the competition between lattice entropy and $\tau J_V$. It is the finite shadow of
  $J_V$ on the stratification of the simplex. The theorem says that the shadow loses nothing.
- It is a statistic that does not see the scale of the rates through the constants $K_F$ (they enter
  only below the leading order), so it is robust in a way that the full law is not; Thm 9.14 makes
  this quantitative at finite horizon, with the start entering only through
  $2R\log(\mu_1/\mu_i)/L$, and Rem 9.15 shows that this is sharp.

### Concrete changes

1. Retitle Section 9 "What the occupation law determines" (or "Coarse functionals and the
   generator"), and replace `sec_reconstruction.tex:13-20` by the three-functional paragraph above.
2. In 9.1 (`sec_reconstruction.tex:24-43`), define the killed chain first, note the shift invariance
   and the reduction to $v\le0$, then define the modal-support map and the strict regions. Keep the
   sentence about ties (lines 41-43) and add the remark of audit 01, M2 (ties of $\Phi'$ are nowhere
   dense for fixed $v$, so strict regions are determined by the observation).
3. State Cor 9.12 before Thm 9.11, as the leading statement of 9.3, in the form "$J_V$ and the
   modal-support map determine the same object, the principal minors"; Thm 9.11 then describes that
   object. The reversible Subsection 9.2 becomes "an explicit finite experiment": $m+d-1$ boundaries,
   design fixed by $R$, $b$ and the labels, minimal by Thm 9.4(a), stable by Thm 9.5.
4. In the introduction, the reconstruction paragraph leads with the Kim and Landim question and the
   stationary-start obstruction, and mentions the controlled boundaries only as the reading device.
5. Part IV uses the same frame: the attraction design is a killing profile of order $t^\gamma$ on the
   complement of a face (after the shift), so the cycle tree is read by the same coarse functional.

---

## 6. Items found while reading that affect the plan

- `sec_dv.tex:231` refers to `sec:boundary-layer`, which does not exist yet (undefined reference in
  the current build).
- The introduction (`sec_intro.tex`) and the plan (278-300) describe only Parts I and II and send the
  reader to the supplement; the abstract is a placeholder (`problem131_chains.tex:69-72`).
- Prop 4.1(d) proves $I_F=I_{F'}$ on subfaces (`sec_firstorder.tex:299-305`) and Prop 3.1 proves
  $J_F=J_V$; after C2 one statement covers both.
- The README of the folder describes the EJP build (`problem131_switching.tex`, 64 pages) and the
  supplement as a proof location; it needs updating after the cuts, with the statements that moved to
  the arXiv-only appendix listed by label key.
- Missing references: Good 1961, Hartfiel and Loewy 1984, Pedler 1971, and (for C10) Bochnak, Coste
  and Roy only if the Zariski route is used. The pending merges of the October 24 memory (Catoni,
  Cirillo, Nardi and Sohier, Freidlin and Wentzell, Olivieri and Vares, Al Ahmadieh, CGGR, Engel and
  Schneider, Loewy, Wolfer and Watanabe) are now in `bib_switching.tex`.
