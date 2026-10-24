# Paper F audit 08: mechanical consistency

Manuscript: `kagey-problems/problem131/paperF/problem131_levy.tex` and its eight inputs
(`sec_intro`, `sec_setting`, `sec_bulk`, `sec_bigjump`, `sec_preparation`, `sec_shape`,
`sec_inverse`, `sec_verify`), state of 2026-10-24 (PDF 62 pages, log has no undefined
references, no multiply defined labels, no overfull boxes). No source file was edited.
Line numbers are by file. Scripts: `refs.py` (labels, refs, cites) and `nums.py`
(the quoted constants) in `scripts/consistency/` of this folder.

A note on the theorem letters. The paper has six lettered theorems, not five:
A = `thm:bulk`, B = `thm:bigjump`, C = `thm:preparation`, D = `thm:mode`,
E = `thm:antimode`, F = `thm:inverse`. The second-order theorem `thm:second-order` is the
numbered Theorem 6.3. Below I use the letters as the PDF prints them.

---

## Findings ranked by severity

### High

**H1. Section 8 is a placeholder, and three places point at it.**
`sec_verify.tex:3` is a single `\proofpending{...}` (red drafting text in the PDF, macro at
`problem131_levy.tex:31-32`). It is cited as if it existed at `sec_intro.tex:56`
(figure caption, "Section~\ref{sec:verify} describes the computations"),
`sec_intro.tex:259-261` and `sec_setting.tex:300-302` ("Section~\ref{sec:verify} records
their formal proofs"). Inside the placeholder: item (iii) lists the certified antimodes at
N in {600,1200,2400,4000}, but Table `tab:antimode` (`sec_shape.tex:688-692`), the figure
(captions.md (b)) and `data/antimode.json` all include N = 8000; item (ii) hard-codes
"Figure~1" instead of `Figure~\ref{fig:atlas}`; item (i) says ball arithmetic "for
N <= 1000", while `atlas_N5000.json` records one ball check, at N = 600. Not mechanical to
fix (the section has to be written), but the N list and the figure reference are.

**H2. The abstract overstates what Example 4.11 shows.**
`problem131_levy.tex:61-62`: "the big-jump theorem needs the local form of regular
variation, which we show is necessary." Example `ex:rv-not-lr` (`sec_bigjump.tex:799-813`)
shows that (RV) and (SPAN) alone do not give Theorem B(b). Remark `rem:wr`
(`sec_bigjump.tex:870-890`) says that two conditions weaker than (LR) are enough on the
ballistic range, and that "We do not pursue the sharp condition." So the paper shows that
*some* local regularity is necessary, not that (LR) is. The introduction gets this right
(`sec_intro.tex:101-102`, "(RV) alone does not control a single bin"). Edit E1.

**H3. The abstract states the antimode with no condition.**
`problem131_levy.tex:58-59`: "the interior minimum near an end sits at the stable scale of
the opposite runs, with an exact second-order coefficient." Theorem E(a)
(`sec_shape.tex:531-539`) needs u_-(j) > 1/mu_- for every j >= 1 (and (LR) for the plus sign
and a fresh plus start). Under E(b) the minimum stays at bounded distance. The introduction
states the condition (`sec_intro.tex:133-144`). Edit E2.

### Medium

**M1. The introduction says that three conditions are nested, and they are not.**
`sec_intro.tex:114-117`: bulk criterion B_n P(D=n) -> 0, big-jump criterion
nu_+(n) = o(T_+(n)), plus-end criterion; "The three conditions are nested." The big-jump
condition controls only the plus atoms, so it implies only the plus half of the bulk
criterion. Theorem C says exactly this (`sec_preparation.tex:96-99`, "which is the plus
half of the bulk criterion"). Also, the nested triple in Theorem C is atom condition =>
big-jump condition => plus half of the bulk criterion, which is not the triple the
introduction lists. Edit E3.

**M2. The introduction writes the boundary layer with "~" where kappa can vanish.**
`sec_intro.tex:96-97`: "P_N(N-j) ~ T_+(N) kappa_+(j)". Theorem B(a)
(`sec_bigjump.tex:56-59`) is the ratio limit P_N(N-j)/T_+(N) -> kappa(j), and
`sec_bigjump.tex:89-95` stresses that kappa(1) = 0 is allowed under (SPAN) (f_-(1) = 0).
Edit E4.

**M3. The introduction's big-jump display drops the floors.**
`sec_intro.tex:88` has f_+(L_k) and T_+(L_k). L_k is not an integer, f_+ is defined only on
integers, and the kernel (`sec_bigjump.tex:22-23`) uses the floor of L_k. Edit E5.

**M4. The introduction's "big-jump zones" bullet misdescribes the kernel.**
`sec_intro.tex:26-30`. (i) "which is of order T_+(N)" is true only on the ballistic range
k - pN of order N. In general the size is Ghat_N(k) = (N/L_k)T_+(floor L_k), which is much
larger near the bulk (`sec_bigjump.tex:66`, Remark `rem:shape-words`). (ii) "Here one of
the two runs is complete and lies in the interior, and the other is still running at slot
N" reads as if both runs were present at once. The kernel is the sum of two alternatives:
the macroscopic run is either complete or censored (`sec_bigjump.tex:25-31`). The abstract
(`problem131_levy.tex:49-50`, "the bin is a sum of a complete run and a run cut by the
horizon") has the same ambiguity in a milder form. Edit E6 (and optionally E6b).

**M5. Ghat_N is typeset two ways.**
The size function is `\hat G_N` in `sec_bigjump.tex:66,69,96,650,656,671` and
`\widehat G_N` throughout `sec_preparation.tex` (defined again at `:33`). It is the same
object. Edit E7.

**M6. Notation clashes (same symbol, two meanings).** These are ordered by how likely they
are to confuse a reader.
- **rho_sigma**: `sec_bulk.tex:185` defines rho_sigma = sup a(m)/a(m-1), and Theorem D(c)
  (`sec_shape.tex:30`) uses rho_sigma for the index of Q_sigma. rho is also used for rho(R)
  (`sec_bulk.tex:537`), the weights rho^{(sigma0)}_i(x) (`sec_bigjump.tex:117`), and the
  index rho in Remark `rem:rho-diagram`.
- **W**: the kernels W_m(j) (`sec_bulk.tex:162-166`), W_theta (`sec_setting.tex:122`), the
  spread W_i(z) (`sec_bigjump.tex:456`) and the window averages W_n (`sec_preparation.tex:53`).
  W_m and W_n are both W with an integer subscript.
- **kappa**: the boundary kernel (`sec_setting.tex:283`), and the constant
  kappa = s/(2c_1 mu_max) in the bulk proof (`sec_bulk.tex:527,530,531,537`). Edit E8.
- **s**: the sum of the means (`sec_setting.tex:73`), the complex Laplace variable in the
  proof of Lemma `lem:stable` (`sec_bulk.tex:79-112`, including "s=-i theta/a(m)"), and a
  dummy in `sec_shape.tex:134`, two lines after s = 2 zeta(alpha) (`:126`).
- **lambda**: the factor lambda_N (`sec_bigjump.tex:47`), the integer giant threshold
  lambda (`:157` onward, in the same section), lambda'_N = ceil((N-j)/(j+1)) (`:232`, which
  looks like a variant of lambda_N), the Laplace modulus (`sec_bulk.tex:84`) and the
  Chebyshev parameter (`sec_shape.tex:331-338`).
- **A, B**: the count A_N and the scale B_N, against A_t(k) and B_t(k) in Proposition
  `prop:final-run` (`sec_setting.tex:421-437`) and Lemma `lem:final-explicit`
  (`sec_shape.tex:249-250`).
- **K**: the count law K^sigma_m and the constant K_alpha, both in `sec_setting.tex:42,93`,
  plus the window constant K everywhere.
- **phi / Phi**: the golden ratio (`sec_intro.tex:130`, `sec_shape.tex:35`), the
  characteristic functions phi_theta and phi (`sec_setting.tex:139,182`), and the argument of
  s (`sec_bulk.tex:83`). Phi is the common bound (`sec_setting.tex:152`) and also
  E[e^{-sX}-1+sX] (`sec_bulk.tex:79`).
- **L**: the run length L_k (`sec_bigjump.tex:11`), the directional defect L^sigma_N
  (`sec_preparation.tex:15`), the length of a complete run (`sec_bigjump.tex:200`) and the
  bulk window L (`sec_bulk.tex:543`).
- **theta**: theta_{sigma,N}, the Fourier variable theta (`sec_bulk.tex:102-109`), and
  theta, theta_delta, theta' in the antimode proof (`sec_shape.tex:587,660,665`).
- **tau**: the dominant sign tau_N (`sec_bulk.tex:336`), the tightness function tau_sigma(z)
  (`sec_bigjump.tex:467`), tau_infty and tau_1 (`sec_preparation.tex:166-167`), and the
  slot indices tau_b and tau_j (`sec_setting.tex:405`, `sec_preparation.tex:230`).
- **Delta**: the defect sup Delta_{sigma,N} (`sec_preparation.tex:16`), the mesh Delta_j
  (`sec_bulk.tex:324`) and the interval Delta (`sec_bigjump.tex:866`).
- **C(j) vs C_j**: the coefficient C(j) (`sec_shape.tex:203`) and the j-dependent constants
  C_j (`sec_bigjump.tex:236`, `sec_preparation.tex:110,408`, `sec_inverse.tex:46`).
- **gamma**: the coefficient gamma^{(sigma0)}_+ (`sec_bigjump.tex:17`) and gamma = eta/2 in
  the proof of Lemma `lem:local-bigjump` (`sec_shape.tex:343-348`).
- **D**: the first-run length D and the error D_N(k) (`sec_bulk.tex:414`). **C_m** is the
  count in the proof of Lemma `lem:green`, against C_lambda(k). **C_3, C_0** are reused
  with different values (`sec_bulk.tex:183` against `sec_preparation.tex:271`;
  `sec_bigjump.tex:323` against `sec_preparation.tex:314`).

**M7. Two families of quoted numbers have no data file.** Everything else checks (item 5
below). Two sets of numbers are not in `data/` and are not produced by
`certify_atlas.py`, `certify_antimode.py` or `make_atlas_figure.py`:
- `sec_bigjump.tex:754-757`: the exact ratios P_N(k)/G_N(k) = 0.354, 1.482, 1.036
  (N = 1200) and 0.337, 1.538, 1.059 (N = 3000). They are consistent with the computed
  limits 0.3126, 1.677, 1.093. The "7 to 8 percent" claim gives 7.8% and 8.3%.
- `sec_preparation.tex:730-732`: the stationary-start ratios 1.0007, 1.0031, 1.0098 at
  N = 2400, and "about half of its value at N = 1200".
Either add them to `data/` with the script that made them, or describe their source in
Section 8.

**M8. Five bibliography entries are never cited.** These are `bvb2024`,
`erickson1970`, `garsialamperti1962`, `sera2024` and `yamazato1978`
(`problem131_levy.tex:88-90,150-152,172-174,248-250,273-275`). Every `\cite` key resolves.
Edit E9 (delete them, or cite them).

### Low

**L1. Statements that assume more than their proofs use.**
- Theorem B (`sec_bigjump.tex:53`) assumes (RV) and (SPAN) for both signs. Part (a) uses
  only (RV) for the plus sign, and the text says so (`:86-87`); the introduction repeats it
  (`sec_intro.tex:97`).
- Theorem F (`sec_inverse.tex:9`) assumes (SPAN) for both signs. Its proof uses Theorem
  B(a), Lemma `lem:end-crude`, Proposition `prop:first-run` and the algebraic inversion
  `eq:renewal-inverse`. None of these uses (SPAN). (RV) for both signs is used.
- Lemma `lem:prep-profile` (`sec_preparation.tex:163`): parts (i)-(iii) need only (RV), and
  only (iv) uses Theorem A.
- Theorem 6.3 (`sec_shape.tex:197`): (RV) and (SPAN) for the minus sign enter only through
  the limit of C(j)/j. This is documented at `:430-432`.
- Corollary `cor:infinite-density` (`sec_bigjump.tex:708`) writes "(LR)" without a sign.
  Read literally, that is both signs; only the plus sign is used.

  I found no proof that uses (LR) or (SPAN) when its statement does not assume it. Every
  appeal to (LR) is either inside an "Assume (LR)" clause or flagged as illustrative
  (`sec_bigjump.tex:249`). Every appeal to the renewal theorem or to Lemma
  `lem:stable`(ii) sits under (SPAN).

**L2.** `sec_intro.tex:25`: "B_N grows like N^{1/alpha}". The two run laws may have
different indices, so B_N is regularly varying with index 1/alpha_* (`sec_preparation.tex:141`).
Edit E10.

**L3.** `sec_bigjump.tex:49`: "lambda_N=1 when b_{+,N}=B_N, for instance when
alpha_+<alpha_-". This holds only for large N. Edit E11.

**L4.** `sec_intro.tex:126-132` omits Theorem D's hypothesis that the preparation satisfies
the bulk criterion, and it uses \mathcal C(\varphi) without a definition or a reference.
Edit E12 adds the reference.

**L5.** `sec_preparation.tex:806`: Remark `rem:rho-diagram`(ii) is stated for a generic sign
sigma, but the extra term is written with nu_+, mu_+ and u_-. Edit E13.

**L6.** The caption (`sec_intro.tex:55-56`) attributes "the finite-N prediction
argmin_j[u_-(j)+C(j)/N]" to Theorem 6.3. The statement j*_N/i_N -> 1 is in Theorem E(a);
Theorem 6.3 supplies only C(j). Edit E14.

**L7.** The bulk outline, Step 2 (`sec_bulk.tex:393`), says the small indices satisfy
m <= epsilon N/(8 max mu). Step 2 itself (`:453-460`) uses m <= k_- < epsilon N with Lemma
`lem:small` at beta = 1/2. The proof is consistent; the outline is not. Edit E15.

**L8.** In Remark `rem:wr` (`sec_bigjump.tex:877-883`), "The first ... The second" refers
back to "two weaker conditions", but an intervening either/or sentence makes "The first"
read as "assumes f_-(1)>0". Suggest "The first weaker condition is ... The second is ...".

**L9.** In the introduction, nu_+ (`sec_intro.tex:115`) is used before it is defined. Also,
"with the two scale ratios of the horizon as coefficients" (`:79-80`) is loose: the
coefficients are (1-p)theta_{+,N} and p theta_{-,N}.

**L10.** Bibliography cosmetics. The key `sera2024` points to a 2026 paper and `bby2023`
to a 2024 paper. `\bibliographystyle{abbrv}` (`problem131_levy.tex:80`) has no effect next
to a manual `thebibliography`.

---

## (1) Labels and references

- 172 labels. None is defined twice, and every `\ref` and `\eqref` resolves (also confirmed
  by the log).
- I read each reference against its target. All point at the intended object, with three
  exceptions, all reported above: `sec:verify` resolves to a placeholder (H1); the caption's
  `thm:second-order` points at the source of C(j), not at the argmin statement (L6); and
  `sec_preparation.tex:38-39` cites Remark `rem:kappa-prep` for a fact that follows from
  `eq:kappa` alone (harmless).
- Labels defined but never referenced (35):
  `sec:intro, sec:intro-picture, sec:intro-results, sec:intro-related,
  sec:intro-organization` (sec_intro 1,18,61,154,240); `sec:runs, hyp:rv, hyp:lr,
  hyp:span, sec:kernels, sec:identities` (sec_setting 3,51,56,60,242,298);
  `eq:bulk-Phi, sec:bulk-profile, sec:bulk-proof` (sec_bulk 93,334,387);
  `sec:giant, sec:boundary-proof, sec:bigjump-proof, sec:bigjump-consequences, rem:wr`
  (sec_bigjump 113,216,278,705,870); `sec:prep-statements, sec:prep-tools, sec:prep-bulk,
  sec:prep-boundary, sec:prep-bigjump, sec:prep-stationary, sec:prep-trim, sec:prep-rho,
  rem:rho-diagram` (sec_preparation 11,135,301,388,436,655,734,785,787);
  `sec:mode, eq:Calpha, eq:mode-interior, rem:ties, sec:second-order, sec:antimode,
  rem:shape-words` (sec_shape 12,39,75,173,185,486,702); `rem:inverse-scope`
  (sec_inverse 186). The hypotheses are referred to by name, "(RV)" and so on, so
  `hyp:*` is fine. `eq:Calpha` should be referenced from the introduction (E12).

## (2) Invocations and the dependency graph

I read every invocation of a numbered or lettered result side by side with its statement.
All match in hypotheses and conclusion, except the reliance on Section 8 (H1). The points
that needed a second look all check:
- Theorem C(d) (`sec_preparation.tex:398-406`) applies Theorem B(a) at horizon N-d.
- Lemma `lem:unif-bigjump`(ii) (`:292-298`) applies the last clause of Theorem B(b), with
  the same hypothesis set.
- Theorem D(a) (`sec_shape.tex:73`) applies Theorem C(b) under the bulk criterion.
- Theorem E (`sec_shape.tex:576`) applies Corollary `cor:bigjump-lower` under exactly the
  hypotheses of Theorem B(b).
- The example (`sec_bigjump.tex:836`) and `eq:far-bound` (`sec_preparation.tex:592`) apply
  Lemma `lem:no-big-run` with eta = 1/32, which gives r = 2.
- Theorem F(b) uses Lemma `lem:end-crude` with (RV) only.

Dependency graph (an arrow means "is used in the proof of"):

```
Sec 2: lem:profile, prop:fresh-identity, prop:first-run, lem:green, prop:final-run, lem:counting
Sec 3: lem:stable(i,iii,iv: RV; ii: SPAN) -> lem:kernels, lem:small, lem:index
       lem:profile-formula, lem:kernels, lem:small, lem:index, prop:fresh-identity -> thm:bulk-restated -> A
       lem:profile -> A(c)
Sec 4: lem:green, lem:counting -> lem:giant
       lem:giant, lem:counting -> B(a)
       lem:stable, lem:truncated -> lem:no-big-run
       lem:giant, (LR) -> lem:two-big-runs
       lem:stable(i,iv) -> lem:spread -> lem:one-big-run (renewal theorem from lem:index)
       lem:giant, lem:no-big-run, lem:two-big-runs, lem:one-big-run -> B(b), B(c), cor:bigjump-lower
       B(b) -> cor:infinite-density; A(c), lem:profile -> rem:no-single-formula, rem:theta
       lem:giant, lem:no-big-run, lem:spread -> ex:rv-not-lr
Sec 5: lem:profile, A(a) -> lem:prep-profile -> lem:green-conc
       B(b) -> lem:unif-bigjump
       prop:first-run, A(a,b), lem:prep-profile -> C(a), C(b)
       prop:first-run, B(a), lem:green -> C(d)
       prop:first-run, lem:unif-bigjump, lem:green-conc, A(b,c), lem:giant, lem:no-big-run, eq:NT-bounds -> C(c)
       C(c), C(d) -> cor:stationary;  A(c), prop:first-run -> cor:no-trim
Sec 6: lem:profile -> lem:profile-uniform;  C(b), lem:profile -> D
       prop:final-run -> lem:final-explicit;  (LR) -> lem:local-bigjump;  lem:sums
       lem:final-explicit, lem:local-bigjump, lem:sums -> thm 6.3 -> prop:uniform-second
       de Bruijn-Erdos -> lem:logconvex
       cor:bigjump-lower, A(c), lem:profile, thm 6.3, prop:uniform-second, eq:second-renewal -> E
Sec 7: lem:counting -> lem:end-crude;  B(a), prop:fresh-identity, prop:first-run, lem:end-crude -> F
```

There is no cycle. No proof uses a result stated after it in reading order. The forward
references are all expository: `sec_setting.tex:66` (Section 4), `sec_bulk.tex:153`
(Lemma `lem:index`), `sec_bigjump.tex:105-111` (the remarks and the corollary that follow),
`sec_preparation.tex:39` (Remark 5.1) and `sec_shape.tex:434` (`eq:second-renewal`). The
only forward dependency is on Section 8 (H1).

## (3) Abstract and introduction against the statements

| Item | Introduction / abstract | Section statement | Verdict |
|---|---|---|---|
| Bulk hypotheses and conclusion | (RV)+(SPAN), whole-row sup, C/B_N (intro 72-77) | A(a),(b) (bulk 10-20) | match |
| Profile description | "two scale ratios as coefficients" (intro 79-80) | (1-p)theta_+ Z_+ - p theta_- Z_- (setting 102) | loose (L9) |
| B_N growth | N^{1/alpha} (intro 25) | RV_{1/alpha_*} | fix (E10) |
| Zone | pN+K lambda_N B_N <= k <= N, double limit (intro 90-91) | B(b) (bigjump 62) | match |
| Kernel | gamma f_+(L_k) + T_+(L_k) kappa_+ (intro 88) | floors of L_k (bigjump 22-23) | fix (E5) |
| gamma asymptotics | gamma(j) ~ js/mu_-^2 (intro 93) | eq:gamma-asymp | match |
| lambda_N | 1 when the plus scale is larger (intro 93-94) | bigjump 47-49 | match (L3) |
| Convention 0/0 | not mentioned; written as (1+o(1)) | B(b): G_N=0 only if P_N=0, ratio read as 1 (bigjump 65) | consistent, implicit |
| Boundary layer | "P_N(N-j) ~ T_+(N) kappa_+(j)", (RV) only (intro 97) | B(a), ratio limit, kappa may vanish | fix (E4) |
| Infinite density | formula (intro 104-108) | cor:infinite-density (bigjump 711-713) | match |
| Preparation criteria | three criteria, "nested" (intro 114-117) | C(b),(c),(d); C 96-99 nests only the plus half | fix (E3) |
| Stationary start | satisfies bulk, fails the other two (intro 119-121) | cor:stationary | match |
| Mode | atom vs H_N/B_N (intro 127-129) | D(b) with the bulk criterion | hypothesis omitted (L4) |
| Golden ratio direction | endpoints win for alpha<phi, bulk for alpha>phi (intro 130-131) | D(d) (shape 35-36) | match |
| Golden constant | 1/C(phi) = 1.288... (intro 132) | C(phi) = 0.7761317205 (shape 43,153); 1/C = 1.2884 (shape 180) | match, recomputed |
| Antimode condition | u_- above 1/mu_-, log-convex (intro 133-135) | E(a): u_-(j) > 1/mu_- for all j>=1; lem:logconvex | match |
| Antimode law | T_-(j*) ~ 2 alpha_+ s/N, j*/argmin -> 1 (intro 137-142) | E(a) (shape 533-537) | match |
| Antimode in abstract | unconditional (abstract 58-59) | E(a) conditional, E(b) bounded | fix (E2) |
| Identification | P_N(N-j)/P_N(N) -> u_-(j); minus end normalized by T_- (intro 147-150) | F(a) (inverse 13-14) | match |
| Thinning | "up to a geometric thinning" (intro 151-152) | rem:thinning | match |
| Necessity of (LR) | "which we show is necessary" (abstract 61-62) | ex:rv-not-lr, rem:wr | fix (E1) |

## (4) Symbols from sec_setting and symbols defined later

The symbols defined in `sec_setting` are used consistently in every section: p, s, B_N,
b_{sigma,N}, theta_{sigma,N}, h_N, H_N, u_sigma, v_sigma, q^sigma_m, u^sigma_m,
K^sigma_m, kappa^{(sigma0)}_+, T_sigma = P(X >= n), and alpha_*. Every later real-argument
extension keeps the ">=" convention (`sec_bulk.tex:39`, `sec_shape.tex:353`), and Frenk's
">" tail is converted explicitly (`sec_shape.tex:495-496`). The exceptions are the dummy
uses of s and the extra meaning of kappa, both in M6. The prepared kernel kappa_+
(`sec_preparation.tex:28`) agrees with the fresh kappa^{(sigma0)}_+ on j >= 1, as stated.

Symbols defined outside `sec_setting` are all defined at or before their first use in the
body: gamma (`sec_bigjump.tex:17`), L_k (`:11`), G_N (`:22`), lambda_N (`:47`), Ghat_N
(`:66`, again at `sec_preparation.tex:33`), rho_i and beta_i (`sec_bigjump.tex:117-121`),
M_N and G_lambda (`:157-161`), f^*_+ (`:180`), L^sigma_N and Delta_{sigma,N}
(`sec_preparation.tex:15-16`), pi_sigma, kappa_+, G^nu_N, Psi_N (`:25-34`), (R nu) and W_n
(`:42-53`), C(j) (`sec_shape.tex:203`), mathcal C(alpha) (`:39`), I_+(v)
(`sec_bigjump.tex:712`). Before its body definition, the introduction uses gamma, L_k,
lambda_N, kappa_+ and C(j) informally, and nu_+ with no definition at all (L9).

## (5) Figure, caption, table and quoted numbers against the data

Verified against `data/` (and recomputed independently where the data give only an
ingredient):
- B_N = 74 (caption, `sec_intro.tex:51`): `atlas_pieces.json` gives B_N = 74.1098, which I
  recomputed as a(5000/s) with T(x) ~ x^{-3/2}/(1.5 zeta(5/2)). Match.
- The axis description (linear on [250,4750], stretched ends) and the junction bands of
  width B_N match `figures/captions.md`.
- In `captions.md`, the zone errors 0.071, 0.38, 0.094 and "relative error below 3e-9"
  match `atlas_pieces.json` (0.0712, 0.3790, 0.0940) and `atlas_N5000.json`
  (a_priori_relative_bound 2.78e-9).
- The antimodes 7, 11, 19, 27, 44 (Table `tab:antimode`) equal `j_star` in
  `antimode.json`. All five are `certified: true`.
- The refined i_N = 7, 12, 20, 28, 45 equal `refined_argmin`. I also recomputed them as the
  argmin of u_-(j)+C(j)/N.
- The leading l_N = 10, 15, 23, 32, 50 equal ceil(`law_T_inverse`) (9.16, 14.25, 22.34,
  31.20, 49.24). I recomputed them as the smallest j with T_-(j) < 2 alpha s/N.
- The column N T_-(j*)/(2 alpha_+ s) = 1.534, 1.498, 1.282, 1.247, 1.186: recomputed
  1.5343, 1.4980, 1.2823, 1.2469, 1.1859. Match.
- The table caption's range "0 <= j <= N/2" matches the data header ("argmin of P_N over
  [N/2, N]") and Theorem E's range (1-p)N with p = 1/2.
- The limit of C(j)/j is 3.0811 (`sec_shape.tex:435`); recomputed 3.08107 (mu = 1.947372,
  s = 3.894745, as in the data). C(j)/j = 4.968, 4.430, 4.041, 3.762, 3.563, 3.422, 3.323:
  recomputed 4.96812, 4.43047, 4.04092, 3.76195, 3.56337, 3.42244, 3.3226. The two forms of
  `eq:Cj` agree to 1e-29.
- The second-order renewal ratios 0.978, 0.994, 0.999 (`sec_shape.tex:501`): recomputed
  0.97823, 0.99452, 0.99863.
- C(phi) = 0.7761317205 and 1/C(phi) = 1.2884 match the recomputed values. So do the bound
  0.9514 (recomputed 0.95136), zeta(phi) = 2.238 >= phi + 1/2 = 2.118, and
  min Gamma = 0.885603 > 0.8856.
- The bulk-profile ratios 0.31, 1.68, 1.09 (`sec_bigjump.tex:752-753`): recomputed 0.3126,
  1.677, 1.093 from the symmetric 3/2-stable density.

Not in the data: see M7. The tex caption is a faithful short form of `captions.md` (L6
aside); it does not quote the N values of panel (b) or the certification.

## (6) Citations

Every `\cite` key exists. Uncited entries: `bvb2024`, `erickson1970`,
`garsialamperti1962`, `sera2024`, `yamazato1978` (M8). Most-cited: `bgt1989` (13
citations), `caravennadoney2019` (4); every other cited entry has 1 to 3 citations. The
`bgt1989` theorem numbers are used consistently: uniform convergence 1.5.2, Potter 1.5.6,
Karamata 1.5.8 and 1.5.10, together with 1.2.1, 1.5.1, 1.5.3, 1.5.12 and 8.4.1 where cited.

## (7) Hypotheses named against hypotheses used

See L1 for the over-assumptions. No proof uses (LR) or (SPAN) beyond what its statement
assumes. Statement by statement:
- Lemma `lem:stable`: parts (i), (iii), (iv) use RV; part (ii) uses SPAN, as stated.
- `lem:small` is RV; `lem:kernels` and `lem:index` are RV + SPAN.
- `lem:profile-formula`, `lem:spread`, `lem:truncated`, `lem:sums` and `lem:end-crude` are
  RV only.
- `lem:two-big-runs` and `lem:local-bigjump` are RV + LR(+).
- `lem:no-big-run` and `lem:one-big-run` are RV + SPAN, with LR(+) only for I_lambda.
- `prop:uniform-second` is RV + LR(+) with no SPAN, which is correct: no renewal theorem is
  used.
- Theorem C(c): the LR(+) part is used in Step 3, and LR on both signs only in the
  window-sufficiency clause, as stated.
- Theorems D and E and Corollary `cor:stationary` use only what they state.

---

## Exact edits for the mechanical items

Each edit gives the file and line, the old text, and the new text.

**E1** `problem131_levy.tex:61-62`
old: `variation and aperiodicity, and the big-jump theorem needs the local form`
`of regular variation, which we show is necessary.}`
new: `variation and aperiodicity, and the big-jump theorem uses the local form`
`of regular variation, and we show that regular variation alone does not suffice.}`

**E2** `problem131_levy.tex:57-59`
old: `ratio threshold, and the interior minimum near an end sits at the stable`
`scale of the opposite runs, with an exact second-order coefficient. The`
new: `ratio threshold. When the renewal mass function of the opposite runs stays`
`above its limit, the interior minimum near an end sits at the stable scale of`
`those runs, with an exact second-order coefficient. The`

**E3** `sec_intro.tex:116-117`
old: `first minus run has the fresh law. The three conditions are nested. When a`
new: `first minus run has the fresh law. The big-jump condition implies the plus`
`half of the bulk criterion. When a`

**E4** `sec_intro.tex:96-97`
old: `$P_N(N-j)\sim T_\plus(N)\kappa_\plus(j)$, which needs only (RV). As $j$ grows,`
new: `$P_N(N-j)/T_\plus(N)\to\kappa_\plus(j)$, which needs only (RV). As $j$ grows,`

**E5** `sec_intro.tex:88`
old: ` P_N(k)=\Bigl[\gamma(N-k)\,f_\plus(L_k)+T_\plus(L_k)\,\kappa_\plus(N-k)\Bigr](1+o(1))`
new: ` P_N(k)=\Bigl[\gamma(N-k)\,f_\plus(\lfloor L_k\rfloor)+T_\plus(\lfloor L_k\rfloor)\,\kappa_\plus(N-k)\Bigr](1+o(1))`

**E6** `sec_intro.tex:27-30`
old: `needs one plus run of macroscopic length, and the law of that run gives the`
`bin its size, which is of order $T_\plus(N)$ with $T_\plus$ the tail of a`
`plus run. Here one of the two runs is complete and lies in the interior,`
`and the other is still running at slot $N$.`
new: `needs one plus run of macroscopic length, and the law of that run gives the`
`bin its size, which is of order $T_\plus(N)$ on the ballistic range, with`
`$T_\plus$ the tail of a plus run. The macroscopic run is either complete and`
`lies in the interior or still running at slot $N$, and the bin is the sum of`
`the two contributions.`

**E6b** (optional) `problem131_levy.tex:49-50`
old: `which one run is macroscopic and the bin is a sum of a complete run and a`
`run cut by the horizon, a renewal boundary layer at each end given by the`
new: `which one run is macroscopic and the bin is the sum of the contributions of`
`a complete run and of a run cut by the horizon, a renewal boundary layer at each end given by the`

**E7** `sec_bigjump.tex:66, 69, 96, 650, 656, 671`: replace every `\hat G_N` by
`\widehat G_N` (six occurrences; leave `\hat L` unchanged).

**E8** `sec_bulk.tex:527, 530, 531, 537`
old (527): `at least $\kappa R$ with $\kappa=s/(2c_1\mu_{\max})$. Lemma~\ref{lem:kernels}`
new (527): `at least $c_8R$ with $c_8=s/(2c_1\mu_{\max})$. Lemma~\ref{lem:kernels}`
In lines 530, 531 and 537 replace `\bar g_\tau(\kappa R)` and `\bar g_\sgn(\kappa R)` by
`\bar g_\tau(c_8R)` and `\bar g_\sgn(c_8R)`.

**E9** `problem131_levy.tex`: delete the five uncited `\bibitem` blocks, `bvb2024`
(88-90), `erickson1970` (150-152), `garsialamperti1962` (172-174), `sera2024` (248-250)
and `yamazato1978` (273-275), or add citations for them.

**E10** `sec_intro.tex:25`
old: `two run-length fluctuations. Here $B_N$ grows like $N^{1/\alpha}$.`
new: `two run-length fluctuations. Here $B_N$ grows like $N^{1/\alpha_*}$ up to a`
`slowly varying factor, with $\alpha_*$ the smaller index.`

**E11** `sec_bigjump.tex:49`
old: `So $\lambda_N=1$ when $b_{\plus,N}=B_N$, for instance when $\alpha_\plus<\alpha_\minus$,`
new: `So $\lambda_N=1$ when $b_{\plus,N}=B_N$, for instance for all large $N$ when $\alpha_\plus<\alpha_\minus$,`

**E12** `sec_intro.tex:132`
old: `tails the bulk wins by the explicit factor $1/\mathcal C(\varphi)=1.288\ldots$. Theorem~\ref{thm:antimode} locates the interior minimum`
new: `tails the bulk wins by the explicit factor $1/\mathcal C(\varphi)=1.288\ldots$, with $\mathcal C$ as in~\eqref{eq:Calpha}. Theorem~\ref{thm:antimode} locates the interior minimum`

**E13** `sec_preparation.tex:806`
old: `that end. In the visible case the regular form of (c) gives the extra term $\nu_\plus(\lfloor L_k\rfloor)(1+\mu_\plus u_\minus(N-k))$,`
new: `that end. In the visible case at the plus end the regular form of (c) gives the extra term $\nu_\plus(\lfloor L_k\rfloor)(1+\mu_\plus u_\minus(N-k))$,`

**E14** `sec_intro.tex:55-56`
old: `finite-$N$ prediction $\arg\min_j[u_\minus(j)+C(j)/N]$ of`
`Theorem~\ref{thm:second-order}. Section~\ref{sec:verify} describes the`
new: `finite-$N$ prediction $\arg\min_j[u_\minus(j)+C(j)/N]$ of`
`Theorem~\ref{thm:antimode}, with $C(j)$ from Theorem~\ref{thm:second-order}. Section~\ref{sec:verify} describes the`

**E15** `sec_bulk.tex:393`
old: `\item Bound the products with a small index $m\le\varepsilon N/(8\max_\sgn\mu_\sgn)$ by`
new: `\item Bound the products with a small index $m<\varepsilon N$ by`

**E16** `sec_verify.tex:3` (inside the placeholder)
old: `(ii) the atlas figure, Figure~1, with`
new: `(ii) the atlas figure, Figure~\ref{fig:atlas}, with`
old: `$N\in\{600,1200,2400,4000\}$`
new: `$N\in\{600,1200,2400,4000,8000\}$`
