# Paper F audit 07: exposition, length and voice

Scope: the whole of `kagey-problems/problem131/paperF` as it stands on
2026-10-24 (`problem131_levy.tex`, `sec_intro`, `sec_setting`, `sec_bulk`,
`sec_bigjump`, `sec_preparation`, `sec_shape`, `sec_inverse`; `sec_verify` is a
placeholder). Voice reference: the first 200 lines of `paperD/sec_intro.tex`
and `paperD/sec_erw_crossing.tex`. Page numbers come from
`problem131_levy.aux` (the PDF is 62 pages: body 1 to 59, references 60 to
62). Page counts per subsection are estimates to about a quarter page. No
paper file was edited. Line numbers are those of the files on disk.

This audit is about length and clarity only. It does not re-check the
mathematics (audits 01 to 05 do that), except where a trim depends on a
mathematical fact, and then I say which one.

---

## 0. Summary

The paper is about 12 pages longer than it needs to be, and the excess is not
in any one proof. It comes from four habits.

1. **The same fact is proved or stated in several places.** The uniform
   properties of the profiles are proved three times (Lemma `lem:profile`
   with `lem:profile-formula`, Lemma `lem:prep-profile`(i)-(iii), Lemma
   `lem:profile-uniform`). The covering identity
   `sum_{m<=j} T_-(m) u_-(j-m) = 1` is proved three times. The renewal
   theorem is invoked from three different sources. The regular-variation
   toolkit (uniform convergence theorem, Potter, Karamata) is re-introduced in
   every section. Theorem `thm:inverse`(b) re-proves Theorem
   `thm:preparation`(d) almost word for word.
2. **Every theorem is followed by a commentary paragraph, and many sections
   end with another one.** These repeat the introduction and each other. The
   double limit of Theorem `thm:bigjump` is explained in four places, the
   right and left deviations of the run sums in four places, and "the proof
   used only ..." in three places in `sec_bulk` alone.
3. **Numerical checks sit inside the proof sections.** There are six of them
   plus a table, and they belong in Section 8.
4. **Restating lemmas that wrap other results.** `thm:bulk-restated`,
   `lem:unif-bigjump`, `lem:end-crude` and `lem:final-explicit` each add a
   statement whose content is already proved elsewhere.

The trims in Section 2 below, all of which leave every proof intact, bring
the paper from 62 to about 47 to 49 pages, counting a 2-page verification
section and the references (the section targets in Section 1 add up to 47).
Moving three optional blocks to the arXiv appendix (as was done for paper D)
gives about 44.

The voice is close to the house style. There are no em-dashes, no colons
inside prose, and only 2 semicolons (both in list items). The main voice
problems are a sentence fragment in the abstract, a few overlong sentences,
mixed "tends to zero" and "tends to $0$", and about a dozen steps that say
"the same argument" or "in the same way" without naming what is reused.

The notation drift is the most serious exposition problem. The worst cases
are `L^sigma_N(b)` (defect) against `L_k` (big-jump length) in the same
theorem, `K^sigma_m(b)` against the window constant `K` in the same theorem,
`A_t`, `B_t` against `A_N`, `B_N`, `rho_sigma` with two meanings, `nu_j`
against `nu_sigma`, and `\varphi` with three meanings. Section 4 has a full
table and a proposed convention.

---

## 1. Per-section table

Verdicts: keep, shorten to N pages, merge, move to an appendix, cut. "App."
means the arXiv appendix, not a separate repository PDF.

### Section 1. Introduction (pp. 1-5, about 4.4 pages). Target 3.3.

| Subsection | Pages | What it does | Verdict | Reason |
|---|---|---|---|---|
| preamble (`sec_intro` 1-16) | 0.4 | Defines `A_N`, `P_N`, physics context | keep | Short and needed. |
| 1.1 The picture (18-59) | 1.1 incl. figure | Four-piece description, Figure 1 | shorten to 0.8 | The bullet for the boundary layer (31-35) is repeated in `sec_bigjump` 3-8 and 25-42 and in `sec_setting` 280-293. Keep the bullets, cut the explanation of `kappa` here to one clause. Caption (46-57) is 12 lines. Move the numerical description ("$B_N=74$", axis stretching) to Section 8 and keep a 4-line caption. |
| 1.2 Results (61-152) | 1.4 | One paragraph per theorem | shorten to 1.1 | Lines 96-109 restate the double-limit discussion that `sec_bigjump` 102-111 and Remark `rem:no-single-formula` give again. Lines 116-117 ("the three conditions are nested") are repeated in Theorem `thm:preparation` 96-99. Lines 132-133 give `1/C(phi)=1.288...`, repeated in Theorem `thm:mode`(d) and Remark `rem:ties`. Keep the displays, drop the repeated justifications. |
| 1.3 Related work (154-238) | 1.2 | Physics, LLT/renewal, the walk, the series | shorten to 1.0 | Keep. The "Local limit theorems" paragraph (179-212) is 34 lines and can lose a third: the sentence on Melbourne-Terhesiu and Caravenna-Doney (196-202) and the sentence on the second-order renewal theorem (208-212, repeated at `sec_shape` 488-499) can each be halved. |
| 1.4 Method and organization (240-261) | 0.4 | Roadmap | shorten to 0.2 | Lines 248-253 repeat the six-step outline of `sec_bulk` 389-399, which itself repeats the step headings. Keep the three identities and one sentence per section. |

### Section 2. Setting, hypotheses and exact identities (pp. 5-13, about 8 pages). Target 5.

| Subsection | Pages | What it does | Verdict | Reason |
|---|---|---|---|---|
| 2.1 Runs, preparation, count (3-45) | 0.8 | Model, `nu`, `Q`, `F^sigma_N`, `K^sigma_m` | keep | Rename `K^sigma_m` (Section 4). |
| 2.2 Hypotheses (47-75) | 0.4 | (RV), (LR), (SPAN), means | keep, add 0.4 | This is the right place for one paragraph of regular-variation facts used everywhere (see trim T6). |
| 2.3 Scales and the moving profile (77-240) | 2.7 | Scales, `h_N`, Lemma `lem:profile` with a 4-step proof | shorten to 1.2, merge | Merge in Lemma `lem:profile-formula` (`sec_bulk` 342-367), Lemma `lem:prep-profile`(i)-(iii) (`sec_preparation` 162-196) and Lemma `lem:profile-uniform` (`sec_shape` 53-69). One lemma, items (a) uniform Lipschitz and sup bounds, (b) uniform sup tail and L1 tail, (c) continuity of `theta -> h_theta` on the compact `Theta` and `N'/N -> 1`, (d) positive minimum on compacts, (e) the conditional formula `eq:bulk-profile`. Step 4 (181-223, about 0.8 page) proves that totally skewed stable densities with `1<alpha<2` are positive on `R`. This is classical. Cite it (for example Sharpe 1969 on zeros of infinitely divisible densities, or Zolotarev's monograph; check the exact statement before citing) or move the proof to the appendix. |
| 2.4 Renewal kernels (242-296) | 1.0 | `u`, `v`, `u_m`, `q_m`, `kappa` | keep | State the renewal theorem here once, with one citation, and the covering identity `eq:cover` here once (it is the second sum of `eq:kernel-sums` in other notation). Define `rho^{(sigma0)}_i(x)` here (now in `sec_bigjump` 117-141), since it is also `A_t` of the final-run identity (Section 4). Fix sentence 286-289 (Section 5, item 2). |
| 2.5 Exact identities (298-532) | 3.1 | Fresh-plus identity, first-run decomposition, Green identity, final-run identity with the `A,B` recursion, counting lemma | shorten to 2.3 | Keep the four propositions and the counting lemma. State the final-run identity directly in the explicit form of `lem:final-explicit` (`sec_shape` 228-257) and delete that lemma. The `A,B` recursion `eq:AB-recursion`, its proof (480-491) and the `O(N^3)` cost (441-443, 493-496) serve only the computation. Move them to Section 8. |

### Section 3. The bulk (pp. 13-23, about 10.5 pages). Target 7.

| Subsection | Pages | What it does | Verdict | Reason |
|---|---|---|---|---|
| preamble, Theorem A, Theorem 3.1 (1-32) | 0.6 | Statement, restatement | shorten to 0.35 | `thm:bulk-restated` (25-32) is part (a) of Theorem A for each sign. Cut it and say "We prove (a); (b) and (c) follow at the end." Lines 3-8 repeat the introduction. |
| 3.1 Classical inputs (34-156) | 2.2 | Lemma `lem:stable`(i)-(iv) | shorten to 1.4 | The regular-variation paragraph (39-50) moves to Section 2. The proof of (i) (77-112, 0.6 page) derives the normalization `K_alpha` from scratch. Cite BGT Section 8.3 or Feller XVII.5 for the domain of attraction and keep only the 6-line check of the constant and the Laplace limit used in (iv). In (iii) drop the aside 139-141. Cut the deviation paragraph 152-156 (the same explanation appears at 395, 480-483 and in Lemma `lem:index`). |
| 3.2 Kernels of one sign (158-332) | 2.8 | (K1)-(K4), Lemmas `lem:kernels`, `lem:small`, `lem:index` | keep, shorten to 2.4 | The proofs are needed. Line 166-167 restates `eq:q-cover`. Line 243 "the second fact about regular variation above" should name the fact (give it a label in Section 2). |
| 3.3 The profile seen from the dominant sign (334-385) | 0.7 | Dominant sign, Lemma `lem:profile-formula`, symmetric form | merge, shorten to 0.2 | Lemma moves to Section 2. The symmetric form and Jacobian (369-385) are used only in the "three regimes" commentary (602-622). Cut both. Keep the definition of `tau_N`. |
| 3.4 Proof (387-662) | 4.6 | Six steps, combination, Theorem A(b),(c) | shorten to 3.2 | Cut the enumerated outline (389-399, 0.5 page), which is a list inside a proof and duplicates the paragraph headings. Keep one 3-sentence roadmap. Cut 480-483 (deviation explanation, 4th time), the "three regimes" paragraph 602-622, Step 6 (624-636) reduced to 2 sentences, and the closing remark 658-662 (the same "used only" points as Step 6). |

### Section 4. Big jumps and the boundary layer (pp. 23-35, about 12 pages). Target 9.5.

| Subsection | Pages | What it does | Verdict | Reason |
|---|---|---|---|---|
| preamble, `L_k`, `gamma`, `G`, `lambda_N`, Theorem B (1-111) | 2.2 | Kernel, heuristics, statement, commentary | shorten to 1.5 | 25-42 explains the kernel. Keep, since the intro only sketches it. The commentary 86-111 (0.5 page) mixes three things: hypotheses used (86-87), why the exact `gamma` matters (87-100), and the double limit (102-111). Keep 2 sentences of the second, cut the first (it reappears at 273-276) and replace the third by a pointer to Remarks `rem:no-single-formula` and `rem:theta`. |
| 4.1 Giant runs (113-214) | 2.0 | Weights `rho`, `beta`, giant identity | keep | Move the definition of `rho` to Section 2 (it equals `A_t`). Rename `beta_i` and `C_lambda`, `I_lambda` (Section 4). |
| 4.2 The boundary layer (216-276) | 1.2 | Proof of B(a) | keep, shorten to 1.0 | 246-251 is an aside about the second sum of the final-run identity. One sentence suffices. Cut 273-276 (the "uses only" paragraph). |
| 4.3 The big-jump zone (278-703) | 5.2 | Karamata form, Lemmas `lem:truncated`, `lem:no-big-run`, `lem:two-big-runs`, `lem:spread`, `lem:one-big-run`, proof of B(b),(c), Corollary `cor:bigjump-lower` | keep, shorten to 4.6 | Karamata `eq:karamata` (285-293) moves to Section 2. Cut the paragraph after `lem:no-big-run` (408-413) to one sentence and the paragraph after `lem:one-big-run` (582-586). The proof of `cor:bigjump-lower` (688-703) repeats pieces of the proof of (b). State the corollary as a sentence at the end of that proof ("the first term of `eq:giant-split` is the only one that used `lambda_N`, so ..."). Two hand-waves to tighten: 346-348 and 493-494 ("costs `O(1)`", "costs `mu_+`"). |
| 4.4 Consequences and an example (705-891) | 3.0 | Infinite density, Remarks `rem:no-single-formula`, `rem:theta`, Example `ex:rv-not-lr`, Remark `rem:wr` | shorten to 2.0 | Remark `rem:no-single-formula`: keep the computation, move the numbers (752-757) to Section 8. Remark `rem:theta`: keep the first paragraph, cut 784-796 to one sentence ("A tail bound of order `exp(-c y^beta)` would replace `lambda_N` by `lambda_N^{1/beta}`. We do not pursue this."). Cut 861-868 to one sentence with the Denisov-Dieker-Shneer citation. Remark `rem:wr` (870-891, 0.45 page): keep 2 sentences (where (LR) enters, and that window regularity at relative width `o(1)` plus (RV) gives (LR)). The verification of the example can move to the appendix if needed (optional, 0.8 page). |

### Section 5. Preparation (pp. 35-47, about 12 pages). Target 8.5.

| Subsection | Pages | What it does | Verdict | Reason |
|---|---|---|---|---|
| 5.1 Statements (11-133) | 2.2 | Defect, kernels, (R nu), `W_n`, Theorem C, Remark `rem:kappa-prep` | shorten to 1.6 | Lines 96-99 (nesting) repeat the intro. Lines 102-104 repeat Remark `rem:theta`. Lines 106-116 prove that (c) contains (d) under (LR). This is a remark, not needed for any proof. Cut to 2 sentences. `\widehat G_N` (33) is `\hat G_N` of `sec_bigjump` 66 under a second macro. Define it once. Remark `rem:kappa-prep`: the example (128-132) can go. |
| 5.2 Tools (135-299) | 2.2 | `lambda_n` uniformity, Lemmas `lem:prep-profile`, `lem:green-conc`, `lem:unif-bigjump` | shorten to 1.0 | `lem:prep-profile`(i)-(iii) merges into Section 2. Keep (iv). `lem:unif-bigjump` restates Theorem B(b) (its proof of (ii), 292-298, is "this is the last clause of Theorem B(b)"). Its part (i) is the bound already proved at `sec_bigjump` 648-650. Replace the lemma by one sentence and one display. Its minus-end clause (278-279) is never used (the sufficiency proof at 586 says so), and then `lambda_{-,n}` (144, 150, 153, 156) is unused too. Cut both. |
| 5.3 The bulk (301-386) | 1.6 | Proofs of C(a), C(b) | keep | Tight. |
| 5.4 The boundary layer (388-434) | 0.6 | Proof of C(d) | keep | Theorem F(b) should cite this proof instead of repeating it. |
| 5.5 The big-jump zone (436-653) | 3.3 | Decomposition, three criteria | keep 2.0, move 1.3 to App. (optional) | The sufficiency of the window condition under (LR) for both signs (574-646, about 1.3 pages) is a sharpness result. It needs its own far-bins bound `eq:far-bound`. If the page budget is tight, state it with a one-line proof sketch and put the proof in the appendix. |
| 5.6 The stationary preparation (655-732) | 1.2 | Corollary `cor:stationary` | keep, shorten to 1.0 | 687-691 re-proves the covering identity. Cite `eq:kernel-sums` or `eq:cover`. Move the numbers 729-732 to Section 8. |
| 5.7 No universal trim (734-783) | 1.0 | Corollary `cor:no-trim` | keep, shorten to 0.85 | Cut 779-783 to one sentence (the first two sentences repeat the construction). |
| 5.8 Regularly varying preparations (785-837) | 0.9 | Remark `rem:rho-diagram` and its verification | cut to 0.3 or move to App. | Every item is an index comparison that the reader can do from Theorem C. Theorem D(c) already handles the endpoint item. Keep a 5-line paragraph at the end of 5.6 with the two lines (stationary on the line of (ii), fresh on the line of (iii)). A whole subsection for a remark is out of proportion. |

### Section 6. The shape of the law (pp. 47-57, about 10.4 pages). Target 8.

| Subsection | Pages | What it does | Verdict | Reason |
|---|---|---|---|---|
| preamble (1-10) | 0.2 | | shorten | Repeats the intro. Two sentences. |
| 6.1 The global mode (12-183) | 2.4 | Theorem D, Lemma `lem:profile-uniform`, proof, Remark `rem:ties` | shorten to 1.7 | Lemma `lem:profile-uniform` is the third copy of the profile facts. Cut. In the proof of (c) (101-107) the regular variation of `B_N` belongs to Section 2. In (d) (112-117) the bulk criterion and the asymptotics of `Q_sigma` repeat Corollary `cor:stationary`(a). Cite it. Paragraph 169-171 can be one sentence. Remark `rem:ties` restates `C(phi)` and `1/C(phi)` (already in the theorem and the intro). Keep one sentence ("on the line `rho_sigma = 1/alpha_*` the comparison depends on slowly varying factors, and we leave it open"). |
| 6.2 Second order (185-484) | 4.7 | Theorem `thm:second-order`, Lemma `lem:final-explicit`, three renewal identities, Lemmas `lem:local-bigjump`, `lem:sums`, proof, Proposition `prop:uniform-second` | shorten to 3.7 | `lem:final-explicit` moves into Proposition `prop:final-run`. `eq:cover` moves to Section 2. In the proof of `lem:local-bigjump`, the exponential Chebyshev bound for `E_3` (330-348, 0.35 page) is Lemma `lem:truncated` with `w=y` and `z=n/2-q mu`. Cite it. The Karamata lines 287-289 and the `T(x)` extension in `lem:sums` (353) go to Section 2. Move the numbers 433-437 to Section 8. |
| 6.3 The antimode (486-720) | 3.3 | Second-order renewal theorem, Lemma `lem:logconvex`, Theorem E, proof, Table 1, Remark `rem:shape-words` | shorten to 2.6 | Move 500-502 (numerical check of Frenk) and Table 1 with 675-680 to Section 8. Remark `rem:shape-words` (702-720, 0.4 page) is a summary of the introduction. Cut it, but keep its last sentence (the law is not claimed monotone between extrema) in the intro. Lines 493-496 discuss `P(X>n)` against `T(n)`. One clause suffices. |

### Section 7. Reading the run laws off the ends (pp. 57-59, about 2.2 pages). Target 1.2.

| Part | Pages | What it does | Verdict | Reason |
|---|---|---|---|---|
| Theorem F, 35-39 | 0.6 | Statement | keep | Replace the hypothesis `L^+_N(j)/(B_N T_+(N)) -> 0` by the equivalent `nu_+(n)=o(T_+(n))` (the proof of C(d), `sec_preparation` 419-426, shows the equivalence). It is easier to read and to check. |
| Lemma `lem:end-crude` (41-67) | 0.45 | `F_m(m-j) <= C_j T_+(m)` | cut | Used only in the proof of (b) and in 169-184. Both become consequences of Theorem C(d). |
| Proof of (a) (69-94) | 0.45 | | keep | The first limit is Theorem B(a) directly. |
| Remark `rem:thinning` (96-124) | 0.55 | Geometric thinning | shorten to 0.35 | Keep the construction and the conclusion. The last sentence (bulk also separates) can stay. Lines 101-104 can be one sentence. |
| Proof of (b) (126-167) | 0.6 | | cut to 0.15 | Lines 128-156 are the proof of Theorem C(d) with the defect assumed small. Write "By Theorem C(d) and the hypothesis, `P_N(N-j)/T_+(N) -> kappa_+(j)`" and keep the inversion 159-166. |
| Paragraph 169-184 | 0.3 | Example of the hypotheses | cut to 2 sentences | With the hypothesis rewritten as `nu_+=o(T_+)`, the example `nu_+=pi_+ f_+` is immediate from (RV) (`f_+=o(T_+)`, `sec_bigjump` `eq:fstar-small`). |
| Remark `rem:inverse-scope` (186-197) | 0.2 | Scope, a fixed-point claim | cut | The last sentence announces unproved work. If kept, keep only the first sentence. |

### Section 8. Verification (placeholder). Target 2 pages.

It should receive: the `A,B` recursion and its cost (from `sec_setting`
433-443 and 480-496), the figure details (from the caption, `sec_intro`
46-57), and the numerical paragraphs listed in trim T3.

### References (pp. 60-62). Target 2.3.

Five entries are never cited: `bvb2024`, `erickson1970`,
`garsialamperti1962`, `sera2024`, `yamazato1978`. Cut them, or cite
`yamazato1978` if it is used for unimodality of `h_N` (stable laws are of
class L and class L is closed under convolution, so each `h_N` is unimodal.
That would let Theorem D(a) speak of "the mode" of the profile.)

---

## 2. Trim list, ranked by pages saved

Each item keeps every proof. "Saved" counts body pages. Items marked (move)
shift material to Section 8 or the appendix.

| # | Trim | Where | Saved |
|---|---|---|---|
| T1 | One profile lemma in Section 2. Merge `lem:profile`, `lem:profile-formula`, `lem:prep-profile`(i)-(iii), `lem:profile-uniform`. Cite positivity of stable densities instead of Step 4. Compress Steps 1-3 (standard Fourier inversion) to a paragraph. | `sec_setting` 109-240; `sec_bulk` 342-385; `sec_preparation` 162-196; `sec_shape` 50-69 | 2.2 |
| T2 | Bulk commentary. Cut the enumerated outline, the deviation explanations (152-156, 480-483), the "three regimes" paragraph, the symmetric form, Step 6 to 2 sentences, the closing remark, and `thm:bulk-restated`. | `sec_bulk` 22-32, 152-156, 369-385, 389-399, 480-483, 602-636, 658-662 | 1.6 |
| T3 (move) | Numerical paragraphs to Section 8: `rem:no-single-formula` 752-757; `sec_preparation` 729-732; `sec_shape` 433-437, 500-502, 675-700 with Table 1; figure caption details `sec_intro` 50-57. | as listed | 0.9 |
| T4 | Theorem F(b) from Theorem C(d). Cut `lem:end-crude`, the proof 128-156, the paragraph 169-184 and Remark `rem:inverse-scope`. | `sec_inverse` 41-67, 126-197 | 1.1 |
| T5 | Remarks that can be one or two sentences: `rem:theta` second paragraph, paragraph after the example, `rem:wr`, `rem:ties`, `rem:shape-words`, `rem:kappa-prep` example, Section 5.8. | `sec_bigjump` 784-796, 861-868, 870-891; `sec_shape` 173-183, 702-720; `sec_preparation` 128-132, 785-837 | 1.9 |
| T6 | One regular-variation paragraph in Section 2.2 (UCT, Potter, Karamata in both forms, `sup_{y<=x} f(y) <= C f(x)`, `T(x/c) <= C_c T(x)`, `N T_+(b_{+,N}) -> s`, `B_N in RV_{1/alpha_*}`, `B_N T_sigma(N) -> 0`, `lambda_N B_N = o(N)`, `eq:NT-bounds`). Then delete the local restatements. | `sec_bulk` 39-50; `sec_bigjump` 218-222, 285-293, 659; `sec_preparation` 49-51, 141, 155-160, 683-685; `sec_shape` 101-110, 112-117, 281-289, 353; `sec_inverse` 62 | 0.7 |
| T7 | `lem:unif-bigjump` replaced by one sentence and one display. Remove `lambda_{-,n}` and the unused minus-end clause. | `sec_preparation` 143-156, 262-299 | 0.6 |
| T8 | Final-run identity in explicit form, using `rho`. Delete `lem:final-explicit`. Move the recursion and its cost to Section 8. Prove `eq:cover` once. | `sec_setting` 420-497; `sec_shape` 224-275; `sec_preparation` 687-691 | 0.7 |
| T9 | Theorem-by-theorem commentary that repeats the intro: after Theorem B (86-111), after Theorem C (96-116), section preambles. | `sec_bigjump` 3-8, 86-111, 273-276, 408-413, 582-586; `sec_preparation` 3-9, 96-116, 779-783; `sec_shape` 3-10, 169-171, 430-432; `sec_inverse` 3-6, 35-39 | 1.0 |
| T10 | Lemma `lem:stable`(i): cite the domain of attraction, keep only the constant check. | `sec_bulk` 77-112 | 0.4 |
| T11 | `E_3` in `lem:local-bigjump` via `lem:truncated`. | `sec_shape` 330-348 | 0.3 |
| T12 | Introduction: caption, organization paragraph, repeated justifications in 1.2, the LLT paragraph of 1.3. | `sec_intro` 46-57, 96-109, 116-124, 179-212, 240-261 | 0.8 |
| T13 | `cor:bigjump-lower` as a closing sentence of the proof of B(b). | `sec_bigjump` 675-703 | 0.2 |
| T14 | Uncited bibliography entries. | `problem131_levy.tex` 88-90, 150-152, 172-174, 248-250, 273-275 | 0.15 |
| T15 (optional, move) | Sufficiency of the window condition (`sec_preparation` 574-646) to the appendix. | | 1.3 |
| T16 (optional, move) | Verification of Example `ex:rv-not-lr` (`sec_bigjump` 816-859) to the appendix. Keep the statement and the two-sentence reason (861-864). | | 0.8 |
| T17 (optional, move) | Proof of positivity in Lemma `lem:profile` to the appendix, if no clean citation is found. | | 0.8 |

Total for T1-T14 is about 12.6 pages, before Section 8 is written (about 2
pages, partly filled by T3 and T8). That gives about 62 - 12.6 + 2 = 51 with
the current section 8 placeholder replaced. Overlaps between items (T2 and T6,
T9 and T12) make the realistic figure about 47 to 49. T15-T17 bring it to
about 44.

### Specific instances by category

**Repeated explanations between the introduction and the sections.**
- Double limit: `sec_intro` 99-102; `sec_bigjump` 102-111; Remark `rem:no-single-formula`; Remark `rem:theta`. Keep the two remarks.
- (LR) is genuine: abstract 60-62; `sec_intro` 101-102; `sec_setting` 65-68; `sec_bigjump` 86, Example `ex:rv-not-lr`, Remark `rem:wr`. Keep the abstract, the example and one sentence in 2.2.
- Nested criteria: `sec_intro` 116; Theorem `thm:preparation` 96-99. Keep the theorem.
- Golden ratio constant: `sec_intro` 129-132; Theorem `thm:mode`(d); Remark `rem:ties` 177-180. Keep the theorem and the intro.
- Boundary layer mechanism: `sec_intro` 31-35; `sec_setting` 280-293; `sec_bigjump` 5-8, 25-42; `sec_shape` 187-194. Keep `sec_setting` and the kernel paragraph of `sec_bigjump`.
- "Every statement at the minus end with signs exchanged": `sec_setting` 295-296; Theorem B line 83; `rem:shape-words` 715-716. Keep `sec_setting`.
- Right and left deviations: `sec_bulk` 152-156, 395, 480-483, and the proof of `lem:index` 294-311. Keep the proof.
- "The proof used only ...": `sec_bulk` 398, 624-636, 658-662; `sec_bigjump` 86-87, 273-276, 582-586; `sec_shape` 430-432. Keep at most one per theorem, as a sentence after the proof.

**Proofs that restate a statement before using it.**
- `sec_bulk` 166-167 restates `eq:q-cover`.
- `sec_bigjump` 334-337 restates the decomposition behind `prop:fresh-identity`.
- `sec_bigjump` 528-534 restates the renewal theorem and `eq:gamma-asymp`.
- `sec_preparation` 175-177 restates the setup of the proof of `lem:profile`.
- `sec_preparation` 213-215 restates the Green identity.
- `sec_preparation` 292-298: the whole proof of `lem:unif-bigjump`(ii) is a restatement of Theorem B(b).
- `sec_shape` 58-62 restates `lem:profile`.
- `sec_shape` 224-226 restates the definition of `S^sigma_r`.
- `sec_shape` 488-499 restates Frenk's hypothesis and discusses `P(X>n)` against `T(n)`.
- `sec_inverse` 128-156 restates the proof of Theorem C(d).

**Lemmas stated more generally than used.**
- `lem:profile` describes every subsequential limit (110-113). Only the bounds, the Lipschitz constant, continuity in `theta`, and the minimum on compacts are used. The subsequence description is used once, in Theorem D(a), and follows from continuity of `theta -> h_theta`.
- `lem:unif-bigjump` has a minus-end clause that is never used.
- `lem:counting` gives `binom(j+1,2)`, and only `(j+1)^2` is used.
- `lem:stable`(iii) is stated for all `j - m mu >= 1`. It is used only for `i >= 4 m mu`. That is harmless, but the remark 139-141 can go.
- `prop:final-run` carries the recursion and the cost, which no proof uses.

**Duplicated classical inputs.**
- Uniform convergence theorem: `sec_bulk` 42-46; `sec_bigjump` 285-286; `sec_preparation` 49-51, 146-148, 159-160; `sec_shape` 281-286.
- Potter's bounds: `sec_bigjump` 286; `sec_preparation` 50, 159; `sec_shape` 343, 635 (each with a citation).
- Karamata: `sec_setting` 65; `sec_bigjump` 287-292 (`eq:karamata`); `sec_shape` 115-116, 287-289; `sec_preparation` 685; and implicitly in `lem:sums`.
- Renewal theorem: `sec_setting` 249 (no citation); `lem:index` (proved); `sec_shape` 423 (cites Feller); used without reference at `sec_bigjump` 31, 529, 591. One statement in 2.4, proved by `lem:index`, and cited by label everywhere.
- Covering identity `sum T_-(m) u_-(j-m) = 1`: `eq:kernel-sums` (second sum, in `q` notation); `sec_preparation` 687-691; `sec_shape` `eq:cover` 262, 266-268.
- `B_N T_sigma(N) -> 0`: `lem:small` 254-255; `sec_preparation` 683-684; `sec_shape` 113-114, 583.
- `lambda_N B_N = o(N)`: `sec_bigjump` 659, 719; `sec_preparation` 155, 531, 559, 716.
- `B_N in RV_{1/alpha_*}`: `sec_preparation` 141; `sec_shape` 101-107; `cor:no-trim` 753.
- Exponential Chebyshev for truncated sums: `lem:truncated`; `lem:local-bigjump` 330-342.
- Extension of `T` to real arguments: `sec_bulk` 38-41; `lem:sums` 353.

---

## 3. Voice violations

Rules checked: short declarative sentences; first person plural; no
semicolons or colons inside prose (colons before displays allowed); no
em-dashes; no "clearly", "obviously", "it is easy to see"; digits for small
numbers; the lemma named at each step; no bullet lists inside proofs; one
name per object.

**Clean.** No em-dashes anywhere (`---` appears only in comment lines 11-18
of `problem131_levy.tex`). No colon inside a prose sentence. No "clearly",
"obviously" or "easy to see".

**Sentence fragment.**
- `problem131_levy.tex` 47-53 (abstract): "A stable bulk at the scale of the larger run fluctuation, a big-jump zone ..., a renewal boundary layer ..., and an atom at each endpoint." has no verb. A colon would fix the grammar but breaks the no-colon rule. Write "The law has four pieces. They are a stable bulk at ..., a big-jump zone ..., a renewal boundary layer ... and an atom at each endpoint."

**Semicolons.**
- `sec_bulk` 14, 15: list items of Theorem A end in semicolons. End them with periods, as the other theorems do.

**Equivalents of "clearly".**
- `sec_bulk` 358: "The bound `\bar H` is immediate." Say why: "Since `g_tau <= ||g_tau||_inf` and `g_{bar tau}` integrates to 1, `h_N <= \bar H`."

**First person plural.**
- `sec_bigjump` 879-881: "So on this range one either assumes ... or keeps only the additive form." Write "we".
- `sec_setting` 309: "The fresh-minus identity is obtained by exchanging" (passive). "Exchanging the signs gives the fresh-minus identity".
- `sec_shape` 430: "The proof uses nothing about the minus runs" is fine. `sec_preparation` 729 "We checked the corollary" is fine, but it moves to Section 8.

**Overlong sentences (over 40 words of prose, math counted as one word).**
- `sec_intro` 133-144 (56 words, with a display in the middle). See Section 5, item 1.
- `sec_intro` 169-174 (53 words). Split after "same rate".
- `sec_setting` 110-114 (54 words, the statement of `lem:profile`). Becomes a list in the merged lemma.
- `sec_setting` 420-424 (54 words). Goes away with T8.
- `sec_preparation` 725-729 (50 words). Split into three sentences, one per term.
- `sec_inverse` 191-196 (57 words). Cut with the remark.
- `sec_bulk` 611-617 (41 words). Goes with T2.
- `sec_inverse` 118-122 (40 words). Split after "sums to one".

**Digits for small numbers.** I applied the rule to numbers that are values
(limits, bounds, multiplicities), not to counts of objects ("two signs",
"three lemmas"), which paper D also writes in words.
- "tends to zero" appears about 25 times (for example `sec_bulk` 45, 58, 122, 366, 431; `sec_preparation` 166, 167, 199, 209, 245, 339, 417, 632; `sec_shape` 61, 93, 109, 113, 348, 584; `sec_setting` 90, 114, 178; `sec_inverse` 155, 179), while `sec_bigjump` 504 and 854 write "tends to `$0$`". Use "tends to `$0$`" throughout.
- "tends to one": `sec_bigjump` 104; `sec_preparation` 826 ("a factor tending to one").
- "equals one": `sec_setting` 113; `sec_shape` 60; `sec_inverse` 108; "sums to one" `sec_inverse` 120. Compare `sec_setting` 230-231 "one of them equals `$1$`".
- "is zero": `sec_bulk` 600; `sec_preparation` 210. "by zero" `sec_setting` 14.

**The lemma used at each step is not named.**
- `sec_bulk` 243: "the second fact about regular variation above". Label it.
- `sec_bulk` 549: "the uniform convergence theorem of Section 3.1". Label it (it moves to 2.2).
- `sec_bigjump` 31, 529, 591; `sec_preparation` 119: "By the renewal theorem". Cite `lem:index`.
- `sec_bigjump` 251: "by the next bound". Name `eq:fstar-small`.
- `sec_bigjump` 346-348: "the argument below changes only by shifts of the index by one, which cost `O(1)` in the deviations". Say which bound absorbs the shift (`lem:stable`(iv) with `y` replaced by `y - mu`).
- `sec_bigjump` 493-494: "which costs `mu_+` in the deviation". Same.
- `sec_bigjump` 506-507: "the same two estimates as for `W_i` apply". Name `tau_+` and `tau_-`.
- `sec_preparation` 150: "in the same way". Goes with T7.
- `sec_preparation` 297: "The minus end is the same argument". Goes with T7.
- `sec_shape` 121: "the same argument shows". Name part (c).
- `sec_shape` 165: "the bulk criterion holds as above". Cite part (d) or `cor:stationary`.
- `sec_shape` 481: "As in the previous proof". Name `eq:cover` and `eq:cover-v`.
- `sec_shape` 423 cites Feller for the renewal theorem, while `sec_bulk` proves it in `lem:index`. Cite your own lemma.

**Bullet lists inside proofs.**
- `sec_bulk` 391-399: an enumerated list inside the proof of `thm:bulk-restated` (the proof runs from 387 to the `\qed` at 647 without a proof environment). Replace by a 3-sentence paragraph (T2). Put the proof in a `proof` environment, or keep the subsection but end it with the closing sentence, not a bare `\qed`.

**One name for one object.**
- The run that contains slot `N`: "final run" (`sec_setting` 420, `sec_bigjump` 159), "run still going at slot `N`" (`sec_intro` 95), "run still running at slot `N`" (`sec_bigjump` 31), "censored run" (`sec_bigjump` 7, 730), "run cut by the horizon" (abstract 50, `sec_intro` 32), "covering run" (`sec_intro` 252). Use "final run" for the object and "censored" as its adjective.
- A plus run with many slots: "giant run" (`sec_bigjump` 159 onward), "big run" (labels `lem:no-big-run`, `lem:two-big-runs`, `lem:one-big-run`), "macroscopic run" (`sec_intro` 27, 32), "long plus run" (`sec_bigjump` 107, 782). Use "giant run" and rename the labels.
- The first run: "preparation", "first run", "delay" (`sec_preparation` 310, 465, 470: "the delays `d <= J`"). Drop "delay".
- The fresh preparation: "fresh start" everywhere except `sec_preparation` 814 "fresh preparation". The stationary preparation is also "equilibrated start" (`sec_intro` 120, abstract 55). Say once in the intro that they are the same.
- "Window": the index window `I^sigma_j(K)` (`sec_bulk` 261), the delay window `|d-n| <= B_n` (`sec_preparation` 53), window regularity (`rem:wr`). Keep "window" for the last two and call the first the "index window".
- "Profile": `h_N` everywhere, but "big-jump profile" in `sec_inverse` 189. Write "big-jump kernel".
- "Count": "plus count", "occupation count" (`sec_intro` 206), "count of the starting sign". Fine, but `A_N` should always be "the plus count".
- The step/slot: the abstract and intro say "right steps", the body says "plus slots". Say once (`sec_setting` 33-35 does) and use "plus slots" after that, including in the abstract's second sentence.

---

## 4. Notation drift

Severity: H = two meanings in the same statement or proof, M = two meanings
in the paper, L = cosmetic.

| Symbol | Meanings and where | Sev. | Proposed convention |
|---|---|---|---|
| `L` | `L_k` big-jump length (`sec_bigjump` 12); `L^sigma_N(b)` directional defect (`sec_preparation` 15), and both appear in Theorem C; `L` run length in `lem:giant` proof (200); `L` window half-width in bulk Step 5 (543); `L_1, L_2` (`lem:two-big-runs`); `L^-` (`sec_preparation` 605) | H | Keep `L_k`. Rename the defect `\mathcal D^\sigma_N(b)`, with `\Delta_{\sigma,N}` its sup as now. Rename the Step 5 window `R` (it is set to `R` anyway at 641). Use `\ell` for run lengths in proofs. |
| `K` | window constant `K` (everywhere); `K_\alpha=-\Gamma(1-\alpha)`; `K^\sigma_m(b)` law of the starting-sign count (`sec_setting` 42), appearing with `K` in Theorem C and its proofs; `C_{\mathrm K}` Karamata constant | H | Keep `K` for the window constant. Rename the count law `\Pi^\sigma_m(b)`. `K_\alpha` is less urgent (it never meets the window constant in one formula). If it is renamed, `\kappa_\alpha` is unavailable (`\kappa` is the boundary kernel), so use `c_\alpha` and rename the different `c_\alpha` of `sec_shape` 132 (see `c` below). |
| `A`, `B` | `A_N` plus count, `B_N` bulk scale; `A_t(k)`, `B_t(k)` start probabilities in `prop:final-run` (`sec_setting` 421-424) and `lem:final-explicit`; `A(x)` Caravenna-Doney function (`sec_bulk` 128) | H | `A_t(k)` is `\rho^{(+)}_{t-k}(k)` of `sec_bigjump` 117 (two symbols for one object). Use `\rho` and define it in 2.4. For `B_t` use `\rho^{\minus}_\cdot` or `\varrho_t(k)`. Call the CD function `\mathcal A`. |
| `\rho` | `\rho_\sigma=\sup a(m)/a(m-1)` (`lem:kernels`); `\rho_\sigma` index of `Q_\sigma` (Theorem D(c), `rem:rho-diagram`); `\rho(R)` bulk error (537); `\rho^{(\sigma_0)}_i(x)` weights | H | `\rho^{(\sigma_0)}_i` for the weights. `\rho_\sigma` for the index of `Q_\sigma` (it is in a theorem). Rename the ratio sup `r_\sigma` and the bulk error `e(R)`. |
| `\nu` | `\nu_\sigma(d)` preparation; `\nu_j(z)` convolution measure (`sec_bigjump` 556, 842-848) | H (Example uses both `\nu_j` and a run law) | Rename the measure `\omega_j` (`\pi_\sigma` is taken). |
| `\varphi`, `\Phi` | golden ratio `\varphi`; characteristic function `\varphi_\theta` (`sec_setting` 139); angle `\varphi` (`sec_bulk` 83-94); `\Phi(t)` common bound (`sec_setting` 152); `\Phi(s)` Laplace remainder (`sec_bulk` 79) | M | Keep `\varphi` for the golden ratio only. Characteristic function `\chi_\theta` (and rename the `\chi` of the antimode proof, see below) or `\widehat h_\theta`. Angle `\vartheta`. Laplace remainder `\Lambda(s)`. |
| `\theta` | `\theta_{\sigma,N}` scale ratio, `\theta\in\Theta`; margin `\theta` in proof of E(b) (`sec_shape` 587); `\theta_\delta`, `\theta'` (660, 665); `\vartheta` exponent (`lem:truncated`) | M | Reserve `\theta` for scale ratios. Margins `\epsilon_*`, `\epsilon'`. |
| `\tau` | dominant sign `\tau_N` (`sec_bulk` 336); slot times `\tau_b` (`lem:green`), `\tau_j` (`lem:green-conc`); tightness `\tau_\sigma(z)` (`lem:spread`); tails `\tau_\infty`, `\tau_1` (`lem:prep-profile`) | M | Keep `\tau` for the dominant sign. Slot times `t_b`. Tightness `\varsigma_\sigma(z)`. Tails merge into `\varepsilon_h` (T1). |
| `\varepsilon_h`, `\tau_\infty` | same object, two names (`sec_bulk` 349; `sec_preparation` 166); also `\sup_{\|x\|>K}h_N` in `lem:profile-uniform` | M | One name, `\varepsilon_h(R)`, in the merged lemma. |
| `\hat G_N`, `\widehat G_N` | same size function defined twice (`sec_bigjump` 66, `sec_preparation` 33) | M | `\widehat G_N`, defined once in Section 4. |
| `G` kernels | `G^{(\sigma_0)}_N` with exact `\gamma` (`eq:G`); `\overline G^{(\sigma_0)}_n` with `(n-L)/\mu_-` (`lem:unif-bigjump`); `G^\nu_N` with `(N-L)/\mu_-` (`eq:G-prep`); `G^{\mathrm{st}}_N` | L | After T7, `\overline G` disappears. Say in Theorem C that `G^\nu_N` uses the limit coefficient. |
| `\eta` | small fraction (`sec_bigjump` 280); `\eta_\sigma(K)`, `\eta(K)` index tails; `\eta_n` bulk error (`sec_preparation` 198); `\eta_N` ratio deviation (484); exponent in `lem:local-bigjump` and `prop:uniform-second`; margin `\eta` (`sec_shape` 95); `\eta'` | M | `\eta` for the fraction of `L_k` only. Index tails `\mathrm{tail}(K)`. Exponents `\delta`. Errors `e_n`. |
| `\lambda` | `\lambda_N` log factor; integer threshold `\lambda=\lceil\eta L_k\rceil`; `\lambda'_N`; modulus `\lambda` in `lem:stable` proof; Chebyshev parameter `\lambda` (`sec_shape` 331) | H (zone `pN+K\lambda_NB_N` and threshold `\lambda` in the same proof) | Keep `\lambda_N`. Use `g` for the giant threshold: `\mathcal G_g`, `M_N<g`. Chebyshev parameter `\vartheta`, as in `lem:truncated`. |
| `\gamma` | `\gamma^{(\sigma_0)}_+(j)`; `\gamma=\eta/2` (`sec_shape` 343); `\gamma_*` | L | Rename the exponent. |
| `\beta` | `\beta_i(x)` weights; `\beta` fraction in `lem:small`; exponent in `rem:theta` | L | Keep `\beta_i`. Fraction `\epsilon_0`. |
| `\kappa` | boundary kernel; `\kappa=s/(2c_1\mu_{\max})` in bulk Step 4 (527) | M | Rename the Step 4 constant `c_8`. |
| `\psi`, `\Psi` | class `\Psi(\omega)` and `\psi` (`sec_bulk` 265); `\Psi_N(k)` preparation term; `\psi(x)` antimode limit (`sec_shape` 602) | M | Keep `\Psi_N`. Class `\mathcal L(\omega)` with members `\phi`. Antimode limit `\Upsilon(x)`. |
| `C` with arguments | `C(j)` second-order coefficient; `C_\lambda(k)` censored term; `\mathcal C(\alpha)` golden constant; numbered constants `C_1,\dots,C_7`, with `C_3`, `C_4` reused with new meanings in `sec_preparation` 271, 462 | M | Rename `C_\lambda(k)`, `I_\lambda(k)` as `\mathrm{Cen}_g(k)`, `\mathrm{Int}_g(k)`. Keep `C(j)`. Let numbered constants be local to a proof, or continue the numbering. |
| `I` | `I^\sigma_j(K)` index window; `I_\lambda(k)`; `I_+(v)` infinite density; halves `I_1, I_2`; blocks `I_i` (`sec_preparation` 580); interval `I` (`sec_setting` 208) | M | After renaming `I_\lambda`, keep `I^\sigma_j(K)` and `I_+(v)`, and call blocks `\mathcal B_i`. |
| `W`, `V` | kernels `W^{\sigma,i}_m`, `V^{\pm,i}_m` (`sec_bulk`); `W_\theta` random variable (`sec_setting` 122); `W_i(z)`, `V_i(z)` spread tails (`sec_bigjump` 456); `W_n` window average; sets `V` (`sec_preparation` 237, 541) | M | Keep `W_n` (in Theorem C). Bulk kernels `\mathsf k^{\sigma,i}_m`. Spread tails `\mathrm{sp}^\rho_i(z)`, `\mathrm{sp}^\beta_i(z)`. Sets `\mathcal V`. |
| `S` | `S^\sigma_m` sums (defined 4 times: `sec_setting` 268, `sec_bulk` 38, `sec_bigjump` 132, `sec_shape` 225); `S_1, S_2` (`sec_bigjump` 340); `S_1,\dots,S_4` (`sec_preparation` 447); set `S` (`sec_preparation` 237); `S=S^+_{J-1}` (`sec_bigjump` 496) | M | Define `S^\sigma_m` once in 2.4. Name the partial sums of probabilities `E_1,\dots,E_4`, as in `sec_preparation` 308. |
| `J` | first-passage index `J_\sigma(j)`; `J` in `lem:spread` (`=J_-(i)`); cutoff `J` (`sec_preparation` 305, 439); `J_0` (`sec_bigjump` 591); `J_N=N^{1-\eta}` (`sec_shape` 451) | M | Keep `J_\sigma(j)`. Cutoffs `d_0`, `j_0`, `j_N`. |
| `M` | `M_N` longest plus run; `M=k/\mu_+` (`sec_bigjump` 373); `M=L_1+L_2` (440); cutoff `M` (`sec_inverse` 173) | L | Local letters `m_+`, `n'`. |
| `R` | remote parameter `R`; probability `R` (`sec_bigjump` 332); `R_i` (`eq:beta-rep`); `R_N(j)` (`sec_shape` 550); `R(n)` (`cor:no-trim`) | M | Keep `R` and `R_N(j)`. `R_i` -> `\xi_i` (the same object is `\xi_j` in `lem:green-conc` 231: two symbols for one object). Call the probability in `lem:no-big-run` `\mathsf P` (`p` and `\Pi^\sigma_m` are taken). |
| `c` | weights `c_W`; `c_\sigma` (`sec_setting` 142); `c_n` (209); `c_0,c_1,c_2` (`sec_bulk` 506), again `c_2,c_3` (`sec_preparation` 568-570); `c_i=i\mu_+/\mu_-` (`sec_bigjump` 496); `c=2\alpha_+s/\mu_-^2` (`sec_shape` 551); `c_\alpha` (132); `c\in(0,1)` (`sec_preparation` 145); `c_*` | M | `c_i=i\mu_+/\mu_-` clashes with numbered constants in the same lemma family. Call it `\bar x_i`. Call the antimode slope `c_{\mathrm a}`, or keep `c` and say it is local. |
| `x` | profile argument `x_{N,k}` (`sec_preparation` 137); `x_k` (`sec_shape` 72); `x` (`sec_bulk` 543); number of plus slots `x` (`sec_bigjump`) | L | Define `x_{N,k}=(k-pN)/B_N` once in 2.3 and use it everywhere. |
| `N-k` | `l` (`sec_setting` 305); `j` (`sec_bigjump`, `sec_preparation`); `k_-` (`sec_bulk` 416); `b` (defect argument); "`l=j=N-k`" (`sec_bigjump` 332) | M | `j=N-k` throughout. In the bulk keep `k_\pm` (the symmetry is useful) but say `k_-=j`. |
| run lengths | `X^\sigma_i` (`sec_setting`); `X_{\sigma,i}` (`sec_bulk` 38, `sec_shape` 240); `X_i`, `Y_i` (`sec_bigjump` 142, `sec_preparation` 227) | M | `X^\sigma_i` throughout, no `Y`. |
| convolution powers | `u^\sigma_m` and `f^{*m}` both used (`sec_shape` 294, 413) | L | `u^\sigma_m` in statements, `f^{*r}` only inside `lem:local-bigjump`. |
| `\epsilon`, `\varepsilon` | `\varepsilon` small constants; `\epsilon_\pm=\pm1` sign factor (`sec_bulk` 338); `\epsilon_m` (197); `\varepsilon_h`, `\varepsilon_N` | M | The two glyphs should not carry different meanings. Write the sign factor `\varsigma_\tau` and use `\varepsilon` only for small numbers. |
| `h`, `g` | `h_N`, `h_\theta`; `h(n)`, `h_i` in the example (`sec_bigjump` 801); `g_\sigma`; `g_N(x)` (`sec_shape` 387) | L | Example: `\epsilon(n)`. `g_N` -> `\Delta_N(x)`. |
| `D` | first-run length `D`; error `D_N(k)` (`sec_bulk` 414) | L | `\mathrm{err}_N(k)`, or `e_N(k)` as in `sec_preparation` 336. |
| `E` | events `E^\pm_i(t,k)`; sums `E_1,E_2,E_3` (`sec_preparation` 308); parts `E_1, E_3` (`sec_shape` 306, 328) | L | Acceptable (local). |
| `\chi`, `\Lambda` | `\chi` (`sec_shape` 599); `\Lambda` in `lem:local-bigjump` (338) and `\Lambda_N=a_-(N)` (597) | L | `\Lambda_N` stays. Rename the first `\Lambda`. |
| `\ell` | `\ell=(v-p)/(1-p)`; summation index `\ell` (`eq:AB-recursion`); `\ell_N` (Table 1) | L | Goes with T3 and T8. |
| `\alpha` | intro 25 "`B_N` grows like `N^{1/\alpha}`" before `\alpha_*` is defined | L | `N^{1/\alpha_*}`, or say "with `\alpha` the smaller index". |

---

## 5. The five hardest sentences, with rewrites

**1. `sec_intro` 133-144.**

> When the renewal mass function $u_\minus$ stays above its limit
> $1/\mu_\minus$, which holds for every strictly log-convex law of the minus
> runs, the minimum sits at $N-j^*_N$ with [display] so $j^*_N$ grows like the
> stable scale of the minus runs, and $j^*_N$ is asymptotic to the minimizer
> of $u_\minus(j)+C(j)/N$ with the exact second-order coefficient $C(j)$ of
> Theorem 6.x.

The sentence runs on through a display and has four clauses after it.

> Suppose that $u_\minus$ stays above its limit $1/\mu_\minus$. This holds
> for every strictly log-convex law of the minus runs. Then the minimum sits
> at $N-j^*_N$ with [display]. So $j^*_N$ grows like the stable scale of the
> minus runs. At finite $N$ the minimizer of $u_\minus(j)+C(j)/N$ predicts
> $j^*_N$ better, and $j^*_N$ is asymptotic to it. Here $C(j)$ is the exact
> second-order coefficient of Theorem 6.x.

**2. `sec_setting` 286-289.**

> The minus runs, read in the time of the minus slots only, form a renewal
> process with interarrival law $X_\minus$ whenever the walk starts with a
> minus run, and a renewal process started at a renewal when it starts with a
> plus run.

The two cases read as different processes, but both are the ordinary renewal
process started at 0. What differs is only whether the epoch 0 is followed by
a plus run, which is what `eq:kappa` records.

> Count time in minus slots only. In both cases the ends of the minus runs
> form a renewal process with interarrival law $X_\minus$, started at $0$. A
> plus run starts right after the $j$-th minus slot exactly when $j$ is a
> renewal epoch, with one exception. For a minus start the epoch $j=0$ is
> followed by the first minus run.

**3. `sec_preparation` 20-22.**

> The defect is the contribution to bin $k$, with $b=N-k$ for $\sgn=\plus$ and
> $b=k$ for $\sgn=\minus$, of a first run of sign $\sgn$ that ends within the
> last $N/2$ slots, scaled by $B_N$.

The subject and its complement are 30 words apart, with a parenthetical
change of variable between them.

> Take a first run of sign $\sgn$ that ends within the last $N/2$ slots.
> Times $B_N$, its contribution to bin $k$ is $L^\plus_N(N-k)$ for
> $\sgn=\plus$ and $L^\minus_N(k)$ for $\sgn=\minus$. So the argument $b$ is
> the number of slots of the opposite sign.

(With the renaming of Section 4, read `\mathcal D` for `L`.)

**4. `sec_preparation` 83-86 (Theorem C(c)).**

> On the interior zones $\varepsilon N\le L_k\le(1-\varepsilon)N$ the term
> $\Psi_N$ is $o(\widehat G_N)$ for every $\varepsilon>0$ if
> $\nu_\plus(n)=o(T_\plus(n))$, and only if $W_n=o(T_\plus(n))$. If (LR) holds
> for both signs, the window condition $W_n=o(T_\plus(n))$ is also sufficient,
> so it is the sharp condition there.

"if A, and only if B" with different A and B is easy to misread as an
equivalence.

> Now restrict to the interior zones $\varepsilon N\le L_k\le(1-\varepsilon)N$,
> and ask that $\Psi_N=o(\widehat G_N)$ there for every $\varepsilon>0$. The
> condition $\nu_\plus(n)=o(T_\plus(n))$ is sufficient for this. The window
> condition $W_n=o(T_\plus(n))$ is necessary, and under (LR) for both signs it
> is also sufficient.

**5. `sec_bigjump` 102-105.**

> At $k=pN+KB_N$ with $K$ fixed the bin is described by the bulk profile, and
> $B_NP_N(k)$ tends to a value of $h_N$ that differs from $B_NG_N(k)$ by a
> factor that tends to one only as $K\to\infty$
> (Remark~\ref{rem:no-single-formula}).

"tends to a value of $h_N$" is not well formed, since $h_N$ moves with $N$,
and two "tends to" in one sentence refer to different limits.

> Fix $K$ and let $k=pN+KB_N$. Theorem~\ref{thm:bulk}(c) gives
> $B_NP_N(k)=h_N(K)+o(1)$. By Remark~\ref{rem:no-single-formula} the ratio of
> $h_N(K)$ to $B_NG_N(k)$ tends to $1$ only as $K\to\infty$.

Runners-up: `sec_bulk` 371-375 (the degenerate profile "at the end point
`theta` of `Theta` ... in the notation of the proof of Lemma 2.1"), which
goes away with T1 and T2; and the abstract fragment 47-53 (Section 3).
