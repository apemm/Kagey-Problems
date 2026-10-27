# Paper F and G finale: research report on the closing pair

**Plan change, 27 October 2026.** The plan changed from one merged paper to 2 papers. F keeps finite
means and gains the finite-mean aging, a compact exposure part and a new framing. G' replaces the
current G and covers infinite means. The earlier version of this report (26 October) planned the
merge. Its findings are kept and sorted by paper below.

Date of this revision: 27 October 2026. This is a planning report, not a draft. It reads the
research notes of `research_notes/Paper FG finale/`, the 5 independent checks in the same folder,
the update section of note 07, the current texts of Papers F and G, the plan `F_plan_v2.md`, the plan
`Plan after C1 - 2026-10-26/PLAN.md` and the README of Problem 131.

**Source key.** Every claim below points to one of these files. Section numbers are those of the
file.

| Key | File |
|---|---|
| N01 | `research_notes/Paper FG finale/01_phase_diagram.md` (dominated regime, phase diagram) |
| N02 | `research_notes/Paper FG finale/02_aging.md` (local aging law) |
| N03 | `research_notes/Paper FG finale/03_alpha_one.md` (the line alpha = 1) |
| N04 | `research_notes/Paper FG finale/04_exposure_queues.md` (queues and exposure) |
| N05 | `research_notes/Paper FG finale/05_literature.md` (literature) |
| N06 | `research_notes/Paper FG finale/06_shape.md` (shape and mode counts) |
| N07 | `research_notes/Paper FG finale/07_novelty.md` (novelty). N07u is its last section, "Update after reading the originals" |
| X08 | `research_notes/Paper FG finale/08_audit_aging.md` (independent check of N02) |
| X09 | `research_notes/Paper FG finale/09_audit_phase.md` (independent check of N01, Section 3) |
| X10 | `research_notes/Paper FG finale/10_audit_shape.md` (independent check of N06) |
| X11 | `research_notes/Paper FG finale/11_audit_alpha_one.md` (independent check of N03) |
| X12 | `research_notes/Paper FG finale/12_audit_exposure.md` (independent check of N04) |
| PF | `kagey-problems/problem131/paperF/` (current Paper F, 80 pages, EJP class) |
| PG | `kagey-problems/problem131/paperG/` (current Paper G, 27 pages) |
| PL1 | `C:\Users\arjun\Downloads\F_plan_v2.md` |
| PL2 | `C:\Users\arjun\Downloads\Plan after C1 - 2026-10-26\PLAN.md` |
| RM | `kagey-problems/problem131/README.md` |

**Label clash.** The notes reuse letters. Note 01 has a Theorem D, note 02 has Theorems A, B, B', C,
note 03 has Theorems A and D, note 06 has Theorems A, B, C. In this report they carry a prefix:
Dom-D (N01), Ag-A, Ag-B, Ag-B', Ag-C (N02), One-A, One-D (N03), Sh-A, Sh-B, Sh-C (N06). The F and G
theorems keep their TeX labels (`thm:bulk`, `thm:local`, and so on). The exposure corollaries of N04
keep the names E1 to E6. The every-N conjectures of N06 Section 7 are called EN1 and EN2 here.

**Status words.** Proved (checked) means an independent check confirmed the proof as written.
Proved with repairs means the check found gaps and named the fix. Written, unchecked means the note
gives a full argument but no independent check exists yet. Heuristic, sketch, conjecture and false
have their usual meaning. Since the last version, notes N03 and N04 have independent checks (X11,
X12), so every note in the folder now has one.

---

## 1. Executive summary

**The object.** Runs of alternating sign with independent lengths, plus runs with law f_+ and
minus runs with law f_-, both with regularly varying tails T_s(n) = P(X_s >= n) of index
alpha_s in (0,2). A_N is the number of plus steps among the first N, and P_N(k) = P(A_N = k). This
is the occupation time of a discrete-time alternating renewal (on/off) process, and equally the
position 2A_N - N of a lattice Levy walk.

**The decision.** 2 papers, not one merged paper.

- **F (finite means, 1 < alpha_+, alpha_- < 2).** Current F, plus the finite-mean aging Ag-C (only
  its zone part Ag-C(d) needs the 3-step repair), plus a compact exposure part (queue cycles have
  finite mean, so the queueing application belongs here), plus the on/off framing and the
  positioning. About 70 to 75 pages. Almost no new mathematics. Submittable in about 3 to 4 weeks.
  About 70% eventual acceptance at EJP.
- **G' (infinite means, replacing current G).** The local Lamperti law (iff the strong renewal
  theorem for both laws), the ends and the initial run, the local aging law (which proves G's
  conjecture and goes beyond the distributional law of Akimoto-Sera-Yamato-Yano 2020), the
  dominated-regime local law, the full shape classification Sh-C (which settles the count for unequal
  tails), and the alpha < 1 mode count if the second-difference theorem Sh-B comes through. About 45
  to 55 pages. About 70% at EJP or Bernoulli.
- The 2 papers cite each other. Together they answer the question of Wang, Schulz, Deng and Barkai
  (2018) on the effect of initial preparation in both regimes: F through `thm:preparation` and Ag-C,
  G' through `thm:initial`, Ag-A and Ag-B.
- **Cut from the journal versions.** The line alpha = 1, Claim K, the every-N conjectures EN1, EN2 and
  Conjecture U. They go to the arXiv builds or to later notes (Section 6).

**Why split.**

1. 2 submissions instead of 1.
2. Easier refereeing. Each paper is on one regime, with one method, at a length a referee will read.
   A merged paper of 95 to 125 pages asks one referee to check both.
3. F goes out early. It needs corrections, one short repair and writing, not new mathematics, so it
   can be on arXiv and at EJP within a month, and the switchback project can cite it.
4. The odds do not favor the merge. A merged paper sits at about 75 to 80% before the length penalty
   of 3 to 5 points, so about 72 to 77% after. 2 papers at about 70% each give more expected
   acceptances, and a rejection of one does not take the other down.

**New against known.** The limits in distribution are classical in every regime (Lamperti 1958,
Takacs 1957, Darling-Kac 1957, Yamato 2026, Akimoto-Sera-Yamato-Yano 2020). The big-jump picture is
known formally in physics (Wang-Schulz-Deng-Barkai 2018, Rebenshtok et al. 2014, Vezzani-Barkai-
Burioni 2019). The local law at one point at the stable scale is partly known for finite means
(Doney 1991, Berger 2019, Melbourne-Pene-Terhesiu 2026). The U/W threshold alpha_c = cos(pi alpha_c/2)
is known (Baldassarri et al. 1999, Godreche-Luck 2001). The local busy-period law is known in
continuous time (Denisov-Shneer 2010) and in the slotted form (Kortchemski 2015, Janson 2012). Not
found in a bounded search (N07, N07u):
- In F: the lattice big-jump kernel with uniform errors, the initial-run theorems, all finite-mean
  aging terms, every exact mode count, the difference bounds (LD), (LD2) for queue cycles, and the
  exposure corollaries for heavy-tailed switchbacks.
- In G': the local Lamperti law and its equivalence with the strong renewal theorem, every local
  statement in the dominated regime, the local aging law, the critical-point count for b != 1 and
  alpha_1, and the exact mode count for alpha < 1.

**What is still missing.**
- F: the 3-step repair of Ag-C(d), 2 small fixes to the exposure corollaries (E1 restriction, E2
  citation), and the corrections of Section 9.2. All short.
- G': the dominated-regime repairs A to F, the Ag-A epsilon fix and the Ag-B typo, Lemma L*, and the
  second-difference local limit theorem Sh-B, which is the one real piece of work. Reading
  Mitov-Yanev 2001 before submission.

**Titles (recommended).**

> F: *Local laws for the occupation time of on/off processes with heavy-tailed, finite-mean periods:
> bulk, big jumps, boundary layers and aging.*
>
> G': *The local Lamperti law: point probabilities for the occupation time of on/off processes with
> infinite-mean periods.*

---

## 2. Framing: the closing pair of the line

### 2.1 The arc

The whole line studies one question: the exact law of the occupation count of a switching process at
a fixed time N, at every lattice point, and in particular how the ends compare with the middle. That
is Kagey's question of when the middle bin is as likely as the endpoints (RM, opening paragraph).

| Paper | Switching mechanism | Run law | What decides end against middle |
|---|---|---|---|
| A | 2-state Markov chain (persistent walk, zero-field Ising chain) | geometric, rate 1-p | the crossing z_N, with z_N + (1/2) log z_N = log N + c_0 + ... |
| B, C1 | d-state chain, rarely switching, P = I + (T/N)Q | geometric on each state | face selection by tau lambda_F + abs(F) - 1, crossings between faces |
| C2 | same | geometric | what the occupation law determines about Q (identifiability) |
| D | elephant walk (memory) | not renewal | crossing x_N = 2 z_N - log(2 pi) + o(1), Luria-Delbrueck law |
| F | alternating renewal, independent runs | regularly varying, index in (1,2) | golden ratio for a stationary or aged start, interior mode for a fresh start |
| G' | same | regularly varying, index in (0,1), balanced or dominated | the end always wins, the U/W thresholds alpha_c and beta_c(alpha) for the bulk |

In A to C2 the runs are geometric, so the walk switches at a fixed rate and the ends win only when
the rate is tuned to about log N / N. Heavy tails make long runs intrinsic. The ends then carry
atoms of order T(N) at any fixed law, and the end-against-middle question becomes a comparison of
exponents: alpha - 1 against 1/alpha (the golden ratio) for finite means, and N T(N) -> infinity
for infinite means. F and G' are the regime where the switching law itself is heavy-tailed, and they
use the same methods as the earlier papers: exact identities by the number of completed runs,
renewal kernels, end layers, and a sign count of the first differences.

### 2.2 How the pair closes the line

- Together they cover the full range 0 < alpha < 2 of index for the run law, so no regime of
  independent runs with regularly varying tails is left out except the boundary lines
  alpha in {1, 2} (Section 7). F takes the square (1,2)^2, G' the diagonal below 1 and the dominated
  regions.
- The rarely switching regime of C1 reappears in 2 places. The dominated regime of G' is a
  heavy-tailed form of rare switching: the heavier side holds the walk, and the lighter side is
  visited about E/T_+(N) times (N01 Section 3). The hard instance proposed for lower bounds in the
  switchback project is a hidden, rarely switching chain, which is the C1 regime (PL2 Section 4,
  item 2).
- The initial-run theorems and the aging laws are the renewal counterparts of the start dependence in
  A and C1. F answers the Wang-Schulz-Deng-Barkai question on initial preparation for finite means,
  G' for infinite means (PL1 Section 0).
- The exposure section of F turns the occupation law into a design statement, which is the bridge to
  the statistics work (Section 8).

None of this language belongs in either paper. Each paper should present itself as a self-contained
treatment of the on/off occupation time in its regime, with one paragraph pointing to the other.
Papers A, C1 and D can be cited once in the related-work paragraph for geometric runs and memory, as F
does now (PF `sec_intro.tex`, paragraph "The walk").

### 2.3 Title options

F:
1. *Local laws for the occupation time of on/off processes with heavy-tailed, finite-mean periods:
   bulk, big jumps, boundary layers and aging.* Recommended. It names the object statisticians and
   queueing people know and the 4 pieces a referee will look for.
2. *The occupation time of an alternating renewal process with regularly varying, finite-mean
   periods, at every point.* Plainer.

G':
1. *The local Lamperti law: point probabilities for the occupation time of on/off processes with
   infinite-mean periods.* Recommended. It leads with the headline theorem.
2. *Occupation times of heavy-tailed on/off processes with infinite means: local Lamperti law,
   dominated regime, aging and shape.* Fuller, less memorable.

### 2.4 Abstract outlines

F (6 sentences):
1. Object: the occupation time A_N of a discrete-time alternating renewal process whose on and off
   periods have regularly varying tails of indices in (1,2), equivalently a lattice Levy walk.
2. Known: the stable limit in distribution. We give P(A_N = k) at every point.
3. A uniform stable local law, a two-term big-jump kernel up to the endpoint with renewal boundary
   layers, and the exact number of modes for all large N.
4. Initial run and aging: sharp criteria for the start, and for observation from time theta N the
   bulk is unchanged while the atom, the layer and the big-jump zone all change.
5. The golden-ratio rule: the endpoint is the global mode iff alpha < phi, for a stationary and for
   every aged start.
6. Application: the exposure law of experiments that switch arm at regenerations of a slotted queue
   with heavy-tailed service, for which the cycle satisfies the difference hypotheses.

G' (6 sentences):
1. Object: the same process with infinite-mean periods, indices in (0,1).
2. Known: the Lamperti law and the Darling-Kac type limits in distribution.
3. Balanced tails: the local Lamperti law holds at one point iff on compacts iff both period laws
   satisfy the strong renewal theorem, with end layers and sharp initial-run criteria.
4. One tail heavier: the time on the lighter side has a local limit law at scale D_N, with no
   renewal condition when its mean is finite or its index exceeds 1/2.
5. Aging: an explicit local mixture with atoms of order 1, which proves the local form of the aging
   law of Akimoto, Sera, Yamato and Yano.
6. Shape: the critical points of the Lamperti density for every asymmetry, with the window
   beta_c(alpha) and the constant alpha_1 = 0.7365, and the exact number of modes for all large N.

---

## 3. Hypotheses used below

(RV) regular variation, (SPAN) span 1, (LR) f_s(n) ~ alpha_s T_s(n)/n, (LB) Doney's bound
f_s(n) <= C T_s(n)/n, (SRT) the strong renewal theorem for alpha < 1, (LD) and (LD2) first and second
difference bounds on f, (EQ) comparable tails, (CMP) comparable slowly varying parts at alpha = 1,
(U) the cycle bound of N02 Section 3, (S) the difference condition on the initial run of N06
Section 3.1, (DSRT) the difference strong renewal theorem.

---

## 4. Paper F: finite means

### 4.1 Theorem list with statuses and repairs

**Core (current F).**

| Result | Statement (short) | Status | Novelty and credit |
|---|---|---|---|
| `thm:bulk` | sup over all k of abs(B_N P_N(k) - h_N((k-pN)/B_N)) -> 0, sup_k P_N(k) <= C/B_N, under (RV), (SPAN), any relation of the 2 scales | Proved in F | Partly known: one point or a window at the stable scale from Doney 1991, Berger 2019 Thm 3.3, Melbourne-Pene-Terhesiu 2026 Thm 1.2, 6.1 (equal index, stationary start). New: uniform in k, all starts, unequal scales (N07 Claim 1a) |
| `thm:bigjump` | P_N(k) = [gamma(N-k) f_+(L_k) + T_+(L_k) u_-(N-k)](1+o(1)) on pN + K lambda_N B_N <= k <= N, layer P_N(N-j)/T_+(N) -> kappa(j) under (RV) only | Proved in F | Partly known: continuum symmetric shape formally in Wang-Schulz-Deng-Barkai 2018 eq. (83), Rebenshtok et al. 2014, Schulz-Barkai 2015, Vezzani-Barkai-Burioni 2019, 2020. New: lattice statement, uniform to the endpoint, both laws, kappa(j) (N07 Claim 3) |
| `cor:infinite-density` | P_N(vN)/T_+(N) -> (1/mu_-)[alpha_+(1-l) l^(-alpha_+-1) + l^(-alpha_+)] | Proved in F | Shape known formally (same sources) |
| `thm:window` | start of the zone sharp up to 1 +- delta when b_{+,N}/b_{-,N} -> 0 | Proved in F | Transfer of Rozovskii 1997 and Denisov-Dieker-Shneer 2008 Section 9.2 to the count. 1 paragraph in the journal build, full in arXiv (PL1 Section 5) |
| `thm:preparation`, `cor:stationary`, `cor:no-trim` | every initial run, bulk criterion B_n nu(n) -> 0, nu_+ = o(T_+) for the layer and zone, closed form for the stationary start | Proved in F | Not found as theorems. Formal structure for the stationary start in Wang-Vezzani-Burioni-Barkai 2019 eqs. (28), (46), (47) |
| `thm:mode` | endpoint against bulk by B_N Q_sigma(N)/H_N, golden ratio for the stationary start, C(phi) = 0.7761 | Proved in F | The exponent identity alpha - 1 = 1/alpha appears in Wang-Li-Haenggi 2016, Cipriani-Denisov-Politi 2005, Lee-Dadswell et al. 2005. The comparison of points and C(phi) are new |
| `thm:second-order`, `thm:antimode` | C(j) in the layer, antimode at T_-(j*) ~ 2 alpha_+ s/N | Proved in F | Inputs Frenk 1982, de Bruijn-Erdos 1953 |
| `thm:mode-count` | exactly M_+ + M_- + 1 modes for all large N under (SPAN), (LR), (LD2), (EQ), fresh or fair start, no ties | Proved in F (the earlier independent check of F found no gap, PL2 Section 1) | Not found (N07 Claim 5). The difference big-jump lemma `lem:diff-bigjump` is partly known: Barbe-McCormick 2009 Thm 2.3.1 for a fixed number of summands (PL2 Section 1, item 2) |

**Aging at theta N (N02 Section 5, X08).** Fresh start at time 0, window of steps
t_a+1, ..., t_a+N, t_a/N -> theta. The straddling run has nu_+(d) ~ (1/s)[T_+(d) - T_+(d + t_a)] at
scale N (N02 Section 1).

| Result | Statement | Status (X08) | Novelty |
|---|---|---|---|
| Ag-C(a) | bulk unchanged: sup_k abs(B_N P_N(k) - h_N(x_{N,k})) -> 0 for every t_a(N) >= 0 | Proved (checked) | Not found. Akimoto 2023 has only the equilibrium start for 1 < alpha < 2 |
| Ag-C(b) | atom P_N(N) ~ N T_+(N)(1 - (1+theta)^(1-alpha))/(s(alpha-1)) | Proved (checked) | Not found |
| Ag-C(c) | layer P_N(N-j)/T_+(N) -> p u_-(j) + 1/s + (1/s)(1 - (1+theta)^(-alpha))(1 + mu_+ u_-(j)) | Proved (checked) | Not found |
| Ag-C(d) | interior zone: P_N(k) = (N - L_k) f_+(L_k)/mu_- + [2 T_+(L_k) - T_+(L_k + t_a)]/mu_- + o(T_+(N)) | Proved with repairs. Bullet 2 of the outline is false (the bound N T(N)^2 fails when L_k - d = o(N)). The 3-step repair is in Section 4.5, item 2 | Not found |
| Golden ratio under aging | endpoint beats bulk iff alpha < phi for every theta in (0, inf) (equal indices), interior at alpha = phi for pure powers | Corollary of Ag-C(a), (b) and `thm:mode`. Not checked independently (X08 Section 4, last line) | New |

All 4 parts of Ag-C interpolate between the fresh start (theta -> 0) and `cor:stationary`
(theta -> inf).

**Exposure in experiments that switch at regenerations (N04, X12).**

| Result | Statement | Status (X12) | Novelty and credit |
|---|---|---|---|
| Reduction | treated slots among the first N in a slotted Geo/G/1 queue that switches arm at every regeneration = A_N with the cycle laws | Written, simulation check (chi^2 = 18.8 on 11 df) | |
| Lemma Q0 | P(C = n) = P(U_n = n-1)/n | Proved as written | Known: Kemperman, van der Hofstad-Keane 2008, Dwass 1969. Continuous-time analogue Denisov-Shneer 2010 Thm 2.1 |
| Lemma Q1 | f_C(n) ~ (1-rho)^(-alpha-1) f_W(n), so (LR) and (SPAN) hold for the cycle | Proved as written | Known in the slotted form: Kortchemski AIHP 2015 eq. (14) (verbatim, slowly varying factor included), Janson Probab. Surveys 2012 Rem. 18.34 (constant case). The continuous-time M/G/1 version is Denisov-Shneer, Queueing Syst. 64 (2010), Cor. 2.2, f_tau(t) ~ f_B((1-rho)t), of which Q1 is the slotted analogue. Credit all 3 (N07u Section 1) |
| Lemma Q2 | f_C(n+1) - f_C(n) = -(alpha+1+o(1)) f_C(n)/n under (LD2) for W | Proved as written | Not found. Denisov-Shneer give first-order equivalences only |
| Claim A | F's `lem:second-bigjump` holds on L >= max(K_1 a(m), L_0, cm) | True, proof complete (every dependency audited, X12 Section 2) | Not found |
| Lemma Q3 | (LD2) for the cycle | Proved (Claims B, C and the assembly checked). (LD2) for queue cycles is closed | Not found |
| E1 | exposure imbalance A_N - pN of order N^(1/alpha), local stable law, P(A_N = k) <= C/B_N | Proved with a restriction: for a random-time start with alpha < phi the uniform local form and the bound C/B_N hold only on 1 <= k < N, since the atoms at k in {0, N} beat every interior value | Distributional limit classical (Takacs 1957). Local form from F |
| E2 | P(N - A_N < eps N) ~ N T_+(N)(eps/mu_-) l_eps^(-alpha_+), l_eps = 1 - eps/(1-p), plus the term l_eps^(1-alpha)/(s(alpha-1)) for a random-time start | Proved. Cite `thm:bigjump`(b) in its additive form for the last delta N points, not (c) | New as a design statement |
| E3 | no switch: P = T_+(N) (fresh) and Q_+(N) + Q_-(N) (random time), exact | Proved as written | |
| E4 | random over fresh no-switch factor ~ (N/(s(alpha-1)))(1 + T_-(N)/T_+(N)) | Proved as written (equal indices in the queue, else alpha_sigma in each term) | |
| E5 | golden-ratio rule with 4 corrections (Section 8.1) | Proved as written, the 4 corrections confirmed | |
| E6 | 3 modes for all large N | Conditional only on strict log-convexity of the total-progeny law, checked numerically (n < 2^14). (LD2) is no longer a condition | |
| Geometric number of cycles | (LR) carries over by Asmussen-Foss-Korshunov 2003 Thm 2(i), Remark 3 | Written, not audited. (LD), (LD2) unchecked | arXiv build of F or the switchback paper |

Correction owed to N04: in the Lemma Q1 paragraph, the global busy-period tail is
P(tau > t) ~ E[nu] P(B > (1-rho)t) with E[nu] = 1/(1-rho) the mean number served, not E[B]. The
global form is De Meyer-Teugels 1980 and Zwart 2001 (reproved by Denisov-Shneer, Thm 3.1). The local
form to quote is Denisov-Shneer Cor. 2.1, 2.2 (N07u Section 1).

**Reframe and positioning (no new mathematics).** Lead with the on/off process and keep the Levy
walk as an equivalent reading. Add the on/off literature (Heath-Resnick-Samorodnitsky 1998,
Taqqu-Willinger-Sherman 1997, Mikosch-Resnick-Rootzen-Stegeman 2002, Starreveld-Bekker-Mandjes),
Akimoto-Sera-Yamato-Yano 2020 for aging, and one paragraph pointing to G' for infinite means.

### 4.2 Novelty and credits

- New: uniformity in k and in the start for the stable local law, the lattice big-jump kernel to the
  endpoint with kappa(j), the initial-run theorems, the golden-ratio comparison of points with
  C(phi), the exact mode count, all aging terms for 1 < alpha < 2, (LD) and (LD2) for queue cycles
  (Q2, Q3, Claim A), and the exposure corollaries E1 to E6 as design statements.
- Credit: Doney 1991, Berger 2019, Melbourne-Pene-Terhesiu 2026 (local law at one point),
  Wang-Schulz-Deng-Barkai 2018 and the physics sources (big-jump shape), Barbe-McCormick 2009 (the
  difference big-jump lemma for fixed m), Rozovskii 1997 and Denisov-Dieker-Shneer 2008 (window),
  Kortchemski 2015, Janson 2012 and Denisov-Shneer 2010 (Q1), De Meyer-Teugels 1980 and Zwart 2001
  (global busy-period tail), Takacs 1957 (global exposure limit), Akimoto 2023 (equilibrium start).
- Do not quote the sentence of Horii-Lefevere-Nemoto 2021 after their eq. (37) as an open problem.
  No follow-up proves it (Horii's 2022 thesis treats it numerically), but it follows directly from
  big-jump large deviations: by their eq. (39), P[N_t < xt] = P(S_floor(xt) > t), and
  P(S_n - n E tau > y) ~ n P(tau > y) uniformly in y >= cn (A.V. Nagaev 1969, S.V. Nagaev 1979,
  Cline-Hsing 1991, Denisov-Dieker-Shneer 2008), so a = 1. If mentioned at all, say this in one
  clause (N07u Section 4).
- Do not repeat Starreveld et al.'s sentence that large deviations of occupation times are
  unstudied. Wang et al. 2018 treated the heavy-tailed case formally (N05 Cautions).

### 4.3 Structure

**Journal build.**
1. **Introduction** (4 pp). The on/off object, the 3 headline theorems in the first 2 pages (uniform
   stable law, big-jump kernel with layers, mode count and golden ratio), then aging and exposure,
   then related work in 1 page with the pointer to G'.
2. **Setting and exact identities** (5 pp). Runs, initial run, the fresh-plus identity, first-run and
   final-run identities, renewal kernels, the Green identity.
3. **The bulk** (`thm:bulk`).
4. **Big jumps and the boundary layer** (`thm:bigjump`, `cor:infinite-density`, a paragraph on the
   window).
5. **The initial run and aging** (`thm:preparation`, `cor:stationary`, Ag-C, the golden ratio under
   aging).
6. **Shape** (`thm:mode`, `thm:antimode`, `thm:mode-count`), proofs in an appendix.
7. **Exposure in experiments that switch at regenerations** (3 to 4 pp). The reduction, Q0 to Q3
   with credit (Q2, Q3 proofs short, Claim A as a remark on F's lemma), E1 to E5, E6 conditional on
   log-convexity.
8. **Open problems** (1 p). Unequal scales for the count (`rem:mode-open`), the line alpha = 1, the
   alpha = 2 lines.
9. **Appendices.** Classical inputs, mode-count proofs (junction argument in full), 1 paragraph on
   the computations with a repository link.

**arXiv build.** Everything in the journal build, plus `thm:window` with proof, the identification
remark (`thm:inverse`, `rem:thinning`), the large mode counts (`ex:runs2`, 13 and 15 modes), the
full mode-count proofs, the full proofs of Q2, Q3 and Claim A with the cycle tables, the
geometric-number-of-cycles remark, and the full account of the computations.

### 4.4 Page estimate

| Block | Pages (journal) |
|---|---|
| Current F | 80 |
| Moved to arXiv: window proof, identification, large examples, computation detail, part of the mode-count proofs | minus 14 to 16 |
| Aging Ag-C and the golden ratio under aging | plus 4 |
| Exposure section | plus 3 to 4 |
| Reframe, positioning, open problems | plus 2 |
| Total | about 70 to 75 |

arXiv build about 85 to 90 pages.

### 4.5 Remaining work in priority order

| # | Item | Difficulty | Odds |
|---|---|---|---|
| 1 | Corrections owed to the current F text (Section 9.2) | 2 to 3 days | 100% |
| 2 | Ag-C(d), 3 steps | 1 week | 90% |
| 3 | Exposure section: write up with the E1 restriction, the E2 citation, the Q1 credit with Denisov-Shneer, the E[nu] fix | 3 to 4 days | 95% |
| 4 | Reframe the introduction, positioning paragraph, pointer to G' | 3 days | 100% |
| 5 | Independent check of the golden ratio under aging (a short corollary) | 1 day | 95% |
| 6 | Journal and arXiv builds, outside read if possible | 3 to 5 days | |
| 7 | Check the published numbering of Kortchemski eq. (14) and Janson Rem. 18.34 (X12 checked arXiv versions only) | 1 hour | |

**Item 2 route (X08 Section 4).** The target is true and F's own proof gives it. Bullet 2 of N02's
outline must be replaced, not expanded.
1. Show that the constants in F's decomposition from the proof of `thm:preparation`(c) depend on the
   initial law only through pi_+- and P(D > J). Then the bound
   abs(P_N(k) - G^nu_N(k) - Psi_N(k)) <= C(eps + r_N + J/(K B_N) + P(D > J)) hat G_N(k) holds for the
   triangular array nu^(N), since sup_N P(D^(N) > J) -> 0 (proved in Ag-C(a)).
2. Prove the triangular-array regular case for Psi_N(k) = sum_{d >= L_k/2} nu^(N)_+(d) Pi^-_{N-d}(N-k).
   Use the Green identity, Green concentration (`lem:green-conc`) within R B_N of L_k, the scale-N
   continuity of nu^(N)_+ from Ag-C(c), and sup_{d >= eps N/2} nu^(N)_+(d) <= C T(N). This gives
   Psi_N(k) = nu^(N)_+(L_k)(1 + mu_+ u_-(N-k)) + o(T(N)).
3. Show kappa^(N)_+(j) -> 1/mu_- as j -> inf uniformly in N: split sum_{d<=j} nu_-(d) u_-(j-d) at
   d = J and use the uniform tail.

Then 1 + mu_+ u_-(N-k) -> s/mu_- and nu_+(L_k) s/mu_- = [T_+(L_k) - T_+(L_k + t_a)]/mu_- + o(T(N)).
Also fix the clash between the start index s and the mean cycle length s in N02 Section 5 (X08
Section 6).

### 4.6 Odds (our judgment)

| Package | EJP eventual acceptance |
|---|---|
| F alone with the corrections of 9.2 | about 65% (PL2) |
| + aging Ag-C and the reframe | about 68% |
| + compact exposure section | about 70% |

The gain comes from removing 2 objections of PL1 Section 0: the unanswered half of the Wang et al.
question in the finite-mean regime, and missing positioning and application. The main residual risk
is a referee who finds 70 pages on one regime of one process long for its significance. An outside
read by a probabilist adds a few points.

---

## 5. Paper G': infinite means

### 5.1 Theorem list with statuses and repairs

**Balanced tails, alpha_+ = alpha_- = alpha < 1, T_-/T_+ -> b in (0, inf) (current G).**

| Result | Statement | Status | Novelty and credit |
|---|---|---|---|
| `thm:local` | N P_N(x_0 N) -> L(x_0) at one point iff uniformly on compacts iff (SRT_+) and (SRT_-) | Proved in G (G's own independent check, PG README) | Not found (N07 Claim 1b). Credit Lamperti 1958 for the density, Caravenna-Doney 2019 for the SRT criterion, Sera 2024 Thm 3.13 as the closest integrated endpoint estimate |
| `cor:lower` | lower half of the local law under (RV) alone | Proved in G | Not found |
| `prop:lambda` | identification with Lamperti's density through the Stieltjes transform | Proved in G | Density classical |
| `thm:ends`(a) | P_N(N-j) = T_+(N) u_-(j) + o(T_+(N)) under (RV) | Proved in G | End structure formal in Wang-Schulz-Deng-Barkai 2018 Section VII.A, eqs. (74)-(77). Credit Godreche-Luck Section 7 too (PL2 Section 3) |
| `thm:ends`(b), (c), `cor:mode` | uniform matching up to (1-delta)N under (LB_+), (SRT_-), global mode at bounded distance from an end | Proved in G under (LB) | New. Without (LB) open (`rem:M0`). Lemma E gives the matching upper bound under (SRT) for alpha != 1/2 |
| `thm:initial`(a)-(f) | exact defect, necessary condition nu = o(1/(n T(n))), sufficient n nu(n) -> 0 under (LB), exact criterion, window condition at the ends | Proved in G | Not found |
| `thm:signs` | lower bound sigma_L + sigma_+ + sigma_- on sign changes | Proved in G | New |
| `thm:shape` (b = 1) | 1 critical point iff alpha <= alpha_c, else 3 | Proved in G. Replaced by Sh-C | Threshold known (BBDG 1999, Godreche-Luck 2001) |
| `conj:count` | equality for all large N | False as stated: exact counts to N = 3000 grow (54 to 338 at alpha = 0.3). The asymptotic disproof is complete once Sh-B (first-difference form) and an alternating-sum lemma are written (X10 Section 3) | Replace by Sh-A |

**Aging at theta N for alpha < 1 (N02 Sections 3, 4, X08).**

| Result | Statement | Status (X08) | Novelty |
|---|---|---|---|
| Lemma 1 | exact law of the straddling run through u_c = renewal mass of f_+ * f_- | Proved, brute force to 6e-16 | Routine |
| Lemma 2 | marked Dynkin-Lamperti law: P(Sigma = +-, D >= rN) -> int_r^inf rho_+-, rho_+-(z) = s_+- (sin pi alpha/pi) theta^alpha z^(-alpha)/(theta + z), s_+ = 1/(1+b), under (RV) only | Proved (checked) | Stated without proof as eq. (18) of Akimoto-Sera-Yamato-Yano 2020 |
| Lemma 4, Cor 4.1 | counting bound sum_i F^-_{n_0+i}(i) <= C m_0 T_-(n_0) + exp(-m_0 T_+(I+1)) + u_-(n_0) sum_{n<=I} T_+(n) | Proved (checked) | New lemma |
| Lemma E | F^-_n(i) <= C T(n) omega_+(i) for i <= n/2 under (SRT), alpha != 1/2 | Proved (checked) | New |
| Ag-A | G's conjecture `rem:aging` holds under (RV), (SPAN), (SRT_+-), without (LB), for initial runs with (H0)-(H2) | Proved with 1 repair: take 0 < delta < eps < min(x_1, 1-x_2)/4, and delta <= 1 - x_2 for Lemma E (X08 Section 1) | New. Proves G's conjecture under a weaker hypothesis |
| Ag-B | N P_N(xN) -> L_{alpha,b,theta}(x) on compacts, (i) under (LB), (ii) for 1/2 < alpha < 1 under (RV), (SPAN) alone, (iii) for alpha < 1/2 under (SRT) and (U) | Proved with 1 typo: insert 1/T(delta N) in the middle display of step (2b) (X08 Section 2) | Global law known: Akimoto-Sera-Yamato-Yano 2020 Thm 2, at the level of a scaling argument. The local law goes beyond it (N07 Claim 7) |
| Ag-B'(a) | atoms P_N(N) -> Q_+(theta) = s_+ (sin pi alpha/pi) B(theta/(1+theta); alpha, 1-alpha), of order 1 | Proved (checked) | Global atoms in ASYY 2020 |
| Ag-B'(b) | layer P_N(N-j) = T_+(N)[c_+(theta) u_-(j) + o(1)], c_+ = s_+ (sin pi alpha/pi) theta^(alpha-1) B(1-alpha,1-alpha) 2F1(1, 1-alpha; 2-2alpha; -1/theta), under (U) | Proved (checked) | Not found. ASYY's c(r) -> 1/2 is the Brownian case b = 1 |
| Non-commuting limits | theta -> 0 gives L but c_+(theta) -> s_+, not 1 | Proved (checked) | ASYY remark after eq. (15) for Brownian motion |
| By-product | global aging law (ASYY Thm 2) under (RV) alone, by Lemma 2 and continuous mapping | Remark (2) of N02 Section 4.4, not separately checked | Gives a proof at the level of a mathematics paper |

Open in N02 Section 7: (M-U) whether (SRT) implies (U) for alpha <= 1/2, (M-1/2) the slowly varying
factor at alpha = 1/2, (M-nec) necessity of (SRT) for the aged law, (M-match) uniform matching of
the aged layer, and rates. These go in the open-problems paragraph.

**The dominated regime (N01 Section 3, X09).** Plus is heavier, 0 < alpha_+ < 1, alpha_- in (0,1) or
(1,2), T_- = o(T_+), (RV) and (SPAN) for both. E = S_+(1)^(-alpha_+) with density phi_E (a rescaled
Mittag-Leffler law, phi_E(0) = 1).
- If mu_- < inf: D_N = mu_-/T_+(N), rho = phi_E.
- If alpha_- < 1: D_N = a_-(1/T_+(N)), rho = density of S_-(1) E^(1/alpha_-). For equal indices with
  b = 0, rho(y) = (sin pi alpha/pi) y^(alpha-1)/(1 + 2 y^alpha cos pi alpha + y^(2 alpha)).
- (W_+): D_N T_+(N) sum_{m <= delta/T_+(N)} u^+_m(N) -> 0.

| Result | Statement | Status (X09) | Novelty |
|---|---|---|---|
| Dom-D(a) | (N - A_N)/D_N converges in law to rho | Known in distribution. Proof: 2 lines from (b), repair A | Known: Yamato 2026 Thm 5.8, Rem. 5.10, 5.12 (Poisson-marked classes, continuous time, so not literally the alternating walk), Darling-Kac 1957 for the mixed case, Cenac-Le Ny-de Loynes-Offret 2019 Section 4.3 (stated without proof for the lattice walk). Lamperti 1958, now read in full, allows 2 sojourn laws but gives only N_n/n -> 1 in the dominated case, with no scaled limit of n - N_n (N07u Section 2). Mitov-Yanev 2001 unread |
| Dom-D(b) | lower half: liminf inf (D_N P_N(N-j) - rho(j/D_N)) >= 0 on compacts, no condition | Proved (checked) | Not found |
| Dom-D(c), mixed region | sup abs(D_N P_N(N-j) - rho(j/D_N)) -> 0 on compacts under (RV), (SPAN) alone | Proved (checked). Harmless slip: a slowly varying factor at alpha_+ = 1/2 | Not found |
| Dom-D(c), alpha_- < 1 | holds if alpha_- > 1/2, and for alpha_- <= 1/2 iff (SRT_-) and (W_+), with (SRT_+) => (W_+) | Sufficiency proved (checked). Necessity proved after the selection steps B and C | Not found. Do not suggest (W_+) is known to be a genuine extra condition (X09 Section 2.3) |
| Dom-D(d), fixed j | P_N(N-j)/T_+(N) -> kappa_+(j), P_N(i)/T_-(N) -> kappa_-(i) under (RV) of the sign concerned | Proved (checked) | Not found as a lattice statement |
| Dom-D(d), uniform matching | P_N(N-j) = T_+(N)[kappa_+(j) Psi(j/D_N) + o(omega(j))] on 0 <= j <= y_2 D_N | Proved with repairs D, E (routine) for alpha_- != 1/2. At alpha_- = 1/2 needs a restriction (repair F) | Not found |
| Lemma Q | (i) q_{m+1}(k) <= C T(k), (ii) lower bound T(k)/2 for m T(k) <= delta_0, (iii) q_{m+1}(k)/T(k) -> phi_E(m T(k)) uniformly on m T(k) <= K | (i), (ii) and (iii) on [eps, K] proved (checked). (iii) near t = 0 needs repair D | New lemma |
| Lemma R | where u(j) lives in m | Proved (checked) | Routine |
| Initial run in this regime | mixed region needs no condition, alpha_- < 1 needs G-type conditions | Outline only (N01 Section 3.7) | Remark in G' |

The claim of N01 that only lemmas already in F and G are used must add 1 external input, the uniform
one-big-jump estimate of repair D (X09 Summary). The claim that a finite-variance lighter law is
covered verbatim needs a short substitute for F's `lem:small` (X09 Section 5).

**Shape for alpha < 1 (N06, X10).**

| Result | Statement | Status (X10) | Novelty |
|---|---|---|---|
| Sh-C | L_{alpha,b} has 3 critical points (min, max, min) iff abs(log b) < beta_c(alpha), else 1 (a minimum). beta_c = 0 for alpha <= alpha_c = 0.594612, closed form on (alpha_c, alpha_1), infinite for alpha >= alpha_1 = 0.736484 (root of alpha = sin pi alpha). Degenerate cases: alpha = alpha_c with b = 1, and abs(log b) = beta_c | Proved (checked). 863 grid cases, 0 mismatches | b = 1 threshold known (BBDG 1999, Godreche-Luck 2001). b != 1 count, beta_c, alpha_1 and the degenerate list not found. Lamperti 1958 has no shape remark (N07u Section 2). Bel-Barkai 2006 saw an asymmetric W at alpha = 0.8 numerically, consistent with alpha_1 |
| Lemma D | u(j) - u(j+1) ~ (1-alpha) u(j)/j for log-convex f | Proved (checked), cosmetic index fix | Not found |
| Lemma P | the prepared profile is eventually strictly decreasing under (S) | Proved (checked) | |
| Sh-A(i) and the count deduction | profile signs copied, count M_+ + M_- + m_L given (i)-(iv) | Proved (checked) | Not found (N07 Claim 5) |
| Sh-A(ii), Theorem L | no antimode in the layer: D_N(j) < 0 for J <= j <= eps N | Proved modulo L* for fresh and fair starts. General (S) starts also need the remainder-length bound sum_n abs(Pi^-_n(j+1) - Pi^-_n(j)) <= C/j (X10 Section 2) | |
| Sh-A(iii), Sh-B | N^2 Delta P_N -> L', N^3 Delta^2 P_N -> L'' on compacts | Sketch. The second-difference limit is indispensable for "exactly once near each critical point" | |
| Sh-A' | log-convex laws, fresh or fair start: exactly 2 + m_L modes | As Sh-A | |
| G1 | `conj:count` false for oscillating starts | Counts reproduced exactly to N = 3000. Asymptotic disproof conditional on Sh-B | arXiv build |
| G2 | at alpha = alpha_c, b = 1, the count depends on the law (Sibuya 3, zeta 2) | Computation only | arXiv build |

### 5.2 Novelty and credits

- New: the local Lamperti law and its equivalence with (SRT) for both laws, the end layers with
  uniform matching, the initial-run criteria, every local statement of the dominated regime with
  Lemma Q, the local aging law with the layer constant c_+(theta), the full critical-point
  classification Sh-C with beta_c and alpha_1, and the exact mode count for alpha < 1 (if Sh-B
  closes).
- Credit: Lamperti 1958 for the density (2 laws and unequal weights allowed, the side choice at the
  regeneration state is i.i.d., so strict alternation needs a one-clause reduction), Caravenna-Doney
  2019 for the SRT criterion, Sera 2024, Godreche-Luck 2001 and Wang-Schulz-Deng-Barkai 2018 for the
  end-layer formula, BBDG 1999 and Godreche-Luck 2001 for alpha_c, Yamato 2026, Darling-Kac 1957 and
  Cenac et al. 2019 for Dom-D(a), Akimoto-Sera-Yamato-Yano 2020 for the global aging law and the
  Dynkin-Lamperti marked law.
- Mitov-Yanev 2001 is still unread (paywalled). Its reference list cites Lamperti's spent-lifetime
  paper (J. Math. Mech. 1958), Dynkin 1955 and Erickson 1970, which suggests it studies the spent
  working time, not the cumulative time A_N. This lowers the chance that it contains Dom-D(a), but
  does not exclude it. Until read, cite it only as limit theorems for alternating renewal processes
  in the infinite-mean case (N07u Section 3).

### 5.3 Structure

**Journal build.**
1. **Introduction** (4 pp). The object, the phase diagram figure, the headline theorems (local
   Lamperti law iff SRT, dominated regime, local aging law), then shape, related work with the
   pointer to F.
2. **Setting and exact identities** (4 pp), citing F for the shared identities and lemmas.
3. **The local Lamperti law** (`thm:local`, `cor:lower`, `prop:lambda`).
4. **The ends and the initial run** (`thm:ends`, Lemma E, `thm:initial`).
5. **Aging** (Lemmas 1, 2, 4, Ag-A, Ag-B, Ag-B').
6. **One tail heavier** (Dom-D with Lemma Q as its own lemma).
7. **Shape** (Sh-C in full, Sh-A as a theorem if Sh-B is done, else Sh-A(i), (ii) and a conditional
   statement of the count, `thm:signs`).
8. **Open problems** (1 p). (M-U), (M-nec), (M-match), alpha_- = 1/2, `thm:ends`(b) without (LB),
   the big-jump kernel toward the lighter end (Claim K) and Conjecture U as one sentence each.
9. **Appendices.** Classical inputs, L* and Sh-B, Lemma Q and the R_N count, the aging proofs of
   Lemmas 2 and 4, 1 paragraph on the computations.

**arXiv build.** Everything above, plus the `conj:count` refutation with tables, the alpha_c degenerate
counts (G2), the every-N counterexamples and conjectures EN1, EN2, Claim K and Conjecture U with all
numerics, and the full proofs.

### 5.4 Page estimate

| Block | Pages (journal) |
|---|---|
| Intro, setting, identities | 8 |
| Local law, ends, initial run (from G) | 15 |
| Aging for alpha < 1 | 8 |
| Dominated regime | 8 |
| Shape: Sh-C | 4 |
| Shape: Sh-A, L*, Sh-B | 6 (2 if Sh-B is stated as a hypothesis) |
| Open problems, appendices of classical inputs | 3 |
| Bibliography | 3 |
| Total | about 51 (about 47 without Sh-B), range 45 to 55 |

arXiv build about 60 to 65 pages.

### 5.5 Remaining work in priority order

| # | Item | Difficulty | Odds |
|---|---|---|---|
| 1 | Corrections owed to the current G text (Section 9.2) | 2 to 3 days | 100% |
| 2 | Dominated-regime repairs A to F, including Lemma Q near 0 | 1 to 2 weeks | 90% (85% with alpha_- = 1/2 handled by restriction) |
| 3 | Aging: the Ag-A epsilon fix, the Ag-B typo, write the section | 1 week | 95% |
| 4 | Lemma L* | 1 to 2 weeks | 80% |
| 5 | Second-difference local limit theorem Sh-B | 3 to 6 weeks | 60% |
| 6 | Read Mitov-Yanev 2001 (library access or interlibrary loan) | request now | |
| 7 | alpha_- = 1/2 by restriction plus one remark (full treatment open-ended, 30%) | 1 day | |

**Item 2. Dominated-regime repairs (X09).**
- **A (part (a)).** Deduce (a) from (b): lower bounds on every compact plus total mass 1 and no atom
  at 0 give convergence in law (X09 Section 1). This makes (a) self-contained, and the paper can
  still credit it as known.
- **B and C (necessity in (c)).** Write the selection steps: for each bad j (or bad n) pick N with
  j/D_N near y, using D_{N+1}/D_N -> 1 (X09 Section 2.3).
- **D (Lemma Q(iii) near t = 0).** Use the uniform one-big-jump estimate
  rho(eps, k) = sup { abs(P(S_m >= x)/(m T(x)) - 1) : x >= k/2, m T(x) <= eps } -> 0 as eps -> 0, after
  k -> inf. Cite Nagaev and Cline-Hsing for x/a_m -> inf and the stable limit for the middle range.
  Then split q_{m+1}(k) by dyadic blocks and use window probabilities, which are o(m T(k)) for
  windows of width o(k), in place of the pointwise local bound (X09 Section 2.4). This is the one
  external input to add.
- **E (R_N for 1 << j << D_N).** In the infinite case use G's `lem:decay`,
  q^-_m(j) <= C T_-(j) e^{-c m T_-(j)}, with the Caravenna-Doney bound. In the mixed case bound the
  part m > delta j by C T_+(N) j/a_+(j) using sum_m q^-_m(j) = 1 (X09 Section 3).
- **F (alpha_- = 1/2).** State the uniform matching for alpha_- != 1/2, or at alpha_- = 1/2 assume
  (SRT_+) with alpha_+ < 1/2 (X09 Section 3).
- **Lemma Q.** Parts (i), (ii) and (iii) on [eps, K] are fine as written. Simpler proof of (ii):
  T(k-r) >= T(k), so q_{m+1}(k) >= (1 - C m T(k)) T(k) (X09 Section 2.1).
- **Smaller.** State that the uniform form of (d) uses (SRT_-) when alpha_- <= 1/2, and give the
  substitute for F's `lem:small` when the lighter law only has a finite variance (X09 Section 5).

**Item 4. Lemma L* (N06 Section 3.3, X10 Section 2).** Statement: under (SPAN), (LR), (LD), with
V_m = f^{*m} and alpha < 1, abs(V_m(n-1) - V_m(n)) <= C m f(n)/n for all m >= 1 and n >= a_m. Route:
take y = n/K and split by the first index with X_i >= y.
- If some jump is at least y, put the difference on that jump, use (LD), and control the cutoff
  boundary term by Doney's local bound at n - y >= n/2.
- If all jumps are below y, split S_m into halves. One half exceeds n/2. Summation by parts moves the
  difference to the other half. Fuk-Nagaev gives P(S_{m/2} >= n/2, max < n/K) <= (C_K m T(n))^(K/2),
  and a truncated Fourier bound of the type of F's `lem:trunc-local` gives sup abs(Delta) <= C_K a_m^(-2).
  Potter closes it once K >= 2 + 4/(alpha - delta).

It is easier than F's alpha > 1 version because there is no centering. About 1 to 2 pages. With L*
written, Theorem L is complete for fresh and fair starts.

**Item 5. Sh-B (X10 Section 2).** Target: uniformly for k/N in compacts, N^2 Delta P_N(k) -> L'(k/N)
and N^3 Delta^2 P_N(k) -> L''(k/N). The second limit is needed to show that the sign of Delta P_N
changes exactly once near each critical point of L. 3 pieces:
- (a) first- and second-difference local limit theorems in space and in m on the scaling range
  m = t/T_+(N). Standard Fourier work under (SPAN) and (RV).
- (b) a second-difference form of L* under (LD2), for the one-giant-run range t < delta. The claim of
  N06 that this range contributes O(delta^2) at the N^2 level is not shown, and nothing is said at
  the N^3 level. This is the real work.
- (c) the second-order defect estimate for (S) starts, plus the remainder-length bound
  sum_n abs(Pi^-_n(j+1) - Pi^-_n(j)) <= C/j for Theorem L with general starts.

Route: take one and two differences inside the proof of G's `thm:local`, as F did for 1 < alpha < 2 in
`thm:bulk-diff`. If (b) stalls, restrict Sh-A to fresh and fair starts and state (iii) as the one
hypothesis. Sh-B with the first difference only also completes the refutation of `conj:count` for
the alpha = 0.3 start (X10 Section 3), once an alternating-sum lemma
N^2 Delta P_N[nu_alt](k) = (-1)^k g(k/N) + o(1) with g(1/2) != 0 is proved.

**Item 7. alpha_- = 1/2.** The (W_+) route and the decay route each lose a ratio of slowly varying
factors, l_-(j)^2 or l_-(j)^2/l_-(D_N)^2, which need not be bounded when l_- oscillates (X09 Section
3). The same boundary appears in the aging note (M-1/2) and in G. State all results for
alpha != 1/2 with the explicit fallback hypotheses, and add one remark.

### 5.6 Odds (our judgment)

| Package | EJP or Bernoulli eventual acceptance |
|---|---|
| G core (local Lamperti law, ends, initial run) + Sh-C | about 60% |
| + dominated regime (Dom-D with repairs) | about 65% |
| + local aging law (Ag-A, Ag-B, Ag-B') | about 68% |
| + full mode count for alpha < 1 (L* and Sh-B) | about 70 to 72% |

Without Sh-B the count is stated conditionally and the paper sits at about 68%. Bernoulli is a good
second venue if EJP declines on scope, since G' is shorter and more classical in flavor than F.

---

## 6. Cut from the journal versions

| Item | Status now | Where it goes |
|---|---|---|
| The line alpha = 1 (N03, X11) | One-A (Theorem A, with Lemmas 1, 2) proved (checked), up to 2 harmless slips (replace "O(abs(m - m_*) L_s)" and "jumps of order 1" by o(sigma)). Prop C proved (checked), and it holds for any regularly varying T_+, not only index -1. The kernel is heuristic only, not a proved leading order: the missing step is the assembly of sum_m u+_m(k) u-_m(j) off the ray, which needs (LR1) and an off-ray local limit (M1). M2 is not a separate gap (it follows from Berger (2.10) by a diagonal argument). The antimode is heuristic, and the N/(4 mu(j*)) column of the note is off (80.9 and 135.9 at N = 1000, 2000, not 66 and 115). In the F-to-G transition, N T(N)/mu(N) -> (1-alpha)/alpha, not 1 - alpha (define eps_N with the de Haan function or as the local index), and the Lamperti-to-Cauchy expansion holds only locally, on abs(t - beta/alpha) = o(1), with exponential true tails beyond. Erickson 1970 still not read in the original | A later short note. Theorem A and Prop C are proved and can stand alone. One sentence in the open problems of each paper |
| Claim K (big-jump kernel toward the lighter end, N01 Section 3.5) | Conjecture. Numerically consistent but slow (ratios 1.04 to 1.45 at N = 4000). Route through F's big-jump section with a local big-jump bound uniform in m <= K/T_+(n) and Lemma Q. Odds 50% for the kernel beyond the window, 30% for the window at (log N)^(1-alpha_+) | arXiv build of G' with the numbers, or a later note |
| Every-N conjectures EN1, EN2 (N06 Section 7) | The fair-start bound "at most 3 modes for every N" is false (exact, N = 39 and 145, X10 Section 4). EN1 (fresh start, CM laws, at most 3 interior maxima for every N) held in all 405 law pairs. EN2 (Sibuya laws, every N, fresh or fair start, at most 3 modes) held for 36 pairs to N = 800. The total positivity route fails for theta_+ + theta_- > 1. EN1 at about 15% | arXiv build of G' with the 2 counterexamples |
| Conjecture U (dominated regime count M_+ + M_- + m_h, threshold curve from (alpha_1, alpha_1) to (1/2, 1)) | Conjecture. The Mittag-Leffler threshold alpha_+ > 1/2 is proved through f'(0) = -1/Gamma(1-2a). Counts agree at every computed N | arXiv build of G' |

These add completeness, not acceptance. None of them should delay either submission.

---

## 7. The phase diagram over (alpha_+, alpha_-)

### 7.1 In words

The tails decide who dominates, not the indices alone (N01 Section 2). When both means are finite,
each side takes a fixed share pN of the time and the heavier tail sets the fluctuation scale
N^(1/alpha_*). This is F. When at least one mean is infinite, the side with the heavier tail
dominates. The lighter side is then visited about E/T_heavy(N) times, and its total time is the
lighter sum run to that random index. Only on the diagonal alpha_+ = alpha_- < 1 with b in (0, inf)
do both sides set the number of cycles together, which gives the Lamperti law at scale N. These are
G'. The dominated regime joins the balanced one continuously at b = 0, since the b -> 0 limit of
L_{alpha,b} read at 1 - x = b^(1/alpha) y is the ratio density rho (N01 Section 2, X09 Section 1). It
joins the finite-mean square at alpha_- = 1 through the relatively stable case (N01 conjecture C1,
N03 Section 6).

Every region has 3 kinds of zone near each end: a bulk, an end layer T_s(N) kappa(j), and either a
big-jump zone (one macroscopic run carries the deviation) or a direct join of layer and bulk.

### 7.2 Table (plus heavier where it matters, mirror by k <-> N - k)

| Region | Paper | Centering and scale | Global limit | Local law and conditions | Ends | Shape | Status and what is open |
|---|---|---|---|---|---|---|---|
| FF: alpha_+, alpha_- in (1,2) | F | pN, B_N = max b_{s,N} ~ N^(1/alpha_*) | (1-p) theta_+ Z_+ - p theta_- Z_-, skewed stable | uniform in all k, (RV), (SPAN) (`thm:bulk`) | big-jump zone + layer + atom at both ends, window when scales differ (`thm:bigjump`, `thm:window`) | M_+ + M_- + 1 modes under (EQ) (`thm:mode-count`) | Proved. Open: unequal scales for the count (`rem:mode-open`), every-N bound |
| BAL: alpha_+ = alpha_- = alpha < 1, b in (0, inf) | G' | 0, N | Lamperti L_{alpha,b} | on compacts iff (SRT_+) and (SRT_-), iff at one point (`thm:local`) | layer joined to bulk, no zone (`thm:ends`, under (LB)) | U or W by Sh-C. Count M_+ + M_- + m_L (Sh-A) | Proved except the count (L*, Sh-B). Open: `thm:ends`(b) without (LB) |
| DOM-mixed: alpha_+ < 1 < alpha_- | G' | count near the plus end, D_N = mu_-/T_+(N) ~ N^(alpha_+) | E (Mittag-Leffler), known in distribution | on compacts under (RV), (SPAN) alone (Dom-D(c)) | plus end: layer joined to bulk at the same height T_+(N). Minus end: big-jump zone (Claim K) with a window at (log N)^(1-alpha_+), then layer | interior mesoscale mode iff alpha_+ > 1/2 (Conj U) | Local law proved. Matching after repairs D, E. Open: Claim K and its window, initial runs, the count |
| DOM-inf: alpha_+ < alpha_- < 1, or equal with b = 0 | G' | D_N = a_-(1/T_+(N)) ~ N^(alpha_+/alpha_-) | S_-(1)/S_+(1)^(alpha_+/alpha_-), known | automatic if alpha_- > 1/2, else iff (SRT_-) and (W_+) | plus end joined, minus end Claim K with no window | interior mode above the curve from (alpha_1, alpha_1) to (1/2, 1) (Conj U) | Local law proved. Matching after repairs, restricted at alpha_- = 1/2. Open: Claim K, count |
| Line alpha_+ = alpha_- = 1 | later note | p_N N, sigma_N ~ N L/mu^2 | A_N/N - p_N -> 0, 1-stable fluctuations | window K sigma_N under (CMP) (One-A) | layer T_+(N) u_-(j) with u_- ~ 1/mu_- -> 0 (Prop C). Kernel heuristic | antimode heuristic | One-A and Prop C proved (checked, X11). Open: M1 and the kernel assembly, M3 |
| Line alpha_+ = 1, alpha_- in (1,2) | later note | p_N N, Cauchy side dominates | totally skewed 1-stable | expected from One-A with F's bookkeeping | | | Expected, not written (N03 Section 6(i)) |
| Line alpha_+ in (0,1), alpha_- = 1 (or alpha_+ = 1, alpha_- < 1) | later note | D_N with truncated means | phi_E (or Z^(-alpha)) | expected, rate 1/log N | | | Sketch (One-D), conjecture C1 of N01 |
| alpha_+ = 1 with infinite mean, alpha_- in (1,2) | open | relatively stable | -C_+ 1-stable after centering | | | | Conjecture C2 of N01 |
| alpha = 2 lines and finite variance | open | Gaussian parts at sqrt(N l(N)) | | | kernel beyond the Nagaev threshold | | Conjecture C4 of N01 |
| T_-/T_+ with no limit, equal indices < 1 | G' remark | | subsequential only | | | | Remark |

Aging overlays every region with alpha < 1 by the mixture L_theta (Ag-B, in G') and every region with
1 < alpha < 2 by the changed ends (Ag-C, in F). The aged versions of the dominated regime are not
done.

### 7.3 The shape phase lines

For balanced infinite means the bulk is W-shaped iff alpha > alpha_c and abs(log b) < beta_c(alpha),
with beta_c -> inf as alpha -> alpha_1 = 0.7365. In the dominated regime the threshold for an interior
mesoscale mode runs from the diagonal point (alpha_1, alpha_1) to alpha_+ = 1/2 at alpha_- = 1, and
continues as alpha_+ > 1/2 for alpha_- > 1 (N06 Sections 2 and 5). So the 2 shape lines meet at
alpha_1, and the picture is continuous across alpha_- = 1. This is a good figure for G': one panel of
the (alpha_+, alpha_-) square with the regions (F's square marked as treated in the companion paper),
one panel of the shape lines. The dominated part of the second panel is conjectural (Conjecture U)
and must be drawn as such.

---

## 8. The statistics connection

### 8.1 What F supplies to the heavy-tailed switchback project

The project is the regenerative switchback with heavy-tailed regeneration (PL2 Section 4, item 1).
A design that switches arm only at regenerations makes the number of treated periods among the first
N exactly A_N, with the cycle laws of the 2 arms as run laws (N04 Section 1). A stable queue has
finite-mean cycles, so the exposure section of F is the one the project cites. G' matters only for
on/off sources, machine availability and systems whose off periods have infinite mean.

- **The exposure law.** E1 gives the local law of the treated count at scale N^(1/alpha). For a fresh
  start the bound C/B_N holds at every point. For a random-time start with alpha < phi it holds only
  on 1 <= k < N, because the no-switch atoms are larger (X12). The treated-share error A_N/N - p is of
  exact order N^(1/alpha - 1), skewed stable and not Gaussian. There is also a deterministic
  imbalance (2p - 1)N when rho_+ != rho_-.
- **Extremes.** E2 gives the probability that one arm gets fewer than eps N periods, and E3 the exact
  probability of no switch at all.
- **Where to start.** E4. The random-time start inflates the no-switch probability by
  (N/(s(alpha-1)))(1 + T_-(N)/T_+(N)), and it adds the complete initial cycle to the big-jump kernel.
  The design rule is to start at a regeneration. Ag-C adds the intermediate case of an experiment
  that starts at time theta N of a running system: the no-switch atom becomes
  N T_+(N)(1 - (1+theta)^(1-alpha))/(s(alpha-1)) and the kernel gains [T_+(L_k) - T_+(L_k + t_a)]/mu_-.
- **The golden-ratio rule, corrected (E5).** Under (RV), (SPAN), equal indices and a random-time
  start, the single most likely value of A_N is an endpoint for all large N when alpha < phi, and
  interior for all large N when alpha > phi. The plan's wording needs 4 corrections, all confirmed by
  X12:
  1. It is not an iff at alpha = phi. On that line slowly varying factors decide. For pure power tails
     F gives an interior mode with C(phi) = 0.776, and for queue cycles the constant is not computed.
  2. No switch is 2 outcomes, and the theorem compares each endpoint atom with the largest interior
     value, not their sum.
  3. It holds for all large N, not for every N.
  4. With unequal indices the criterion is per arm, alpha_sigma - 1 < 1/alpha_*.
  The same threshold holds for a start at a typical time of a system that ran in control only, and
  for every aged start at theta N (Ag-C). For a fresh start the mode is always interior.
- **The start factor, corrected.** The plan's factor of order N/(alpha-1) is right in order. The exact
  same-arm factor is N/(s(alpha-1)), and the random start adds the atom of the second arm (E4).
- **Queue-cycle hypotheses.** For the slotted Geo/G/1 queue with locally regularly varying service,
  (LR) and (SPAN) hold for the cycle with f_C(n) ~ (1-rho)^(-alpha-1) f_W(n) (credit Kortchemski 2015,
  Janson 2012, and Denisov-Shneer 2010 for the M/G/1 version), (LD) holds by Q2, and (LD2) holds by
  Q3 with Claim A, now closed. Both arms share the service law, so (EQ) holds. Switching after a
  geometric number of cycles keeps (LR) by Asmussen-Foss-Korshunov 2003.
- **Which regimes matter for queues.** The FF region. An arm that changes the service tail index
  breaks (EQ), and the count is then open (`rem:mode-open`).

### 8.2 What the project still needs beyond F

1. **Joint renewal-reward stable limits.** The effect estimator uses rewards accumulated over cycles
   together with the time spent in each arm. One needs the joint stable limit of (sum of rewards,
   sum of cycle lengths) per arm, and its local or at least tail form, when the cycle has infinite
   variance and the reward is correlated with the cycle length. F gives only the time coordinate.
2. **Ratio estimators.** The natural estimators are ratios of reward sums to exposure. With infinite
   variance the delta method needs the joint stable law, and the denominator can be small with
   probability of order T(N) (the atoms and the big-jump zone). F's bounds control that event, but the
   limit law of the ratio, its bias and valid intervals (self-normalized or subsampling) are new work.
3. **Interval designs.** The comparison with fixed-interval switchbacks, where the heuristic rate is
   about T^(-(alpha-1)/(2alpha-1)) against T^(1/alpha-1) for regenerative designs (PL2 Section 4).
   This needs a carryover structure for heavy-tailed regeneration that F does not have.
4. **Lower bounds.** A minimax lower bound over all designs and estimators, through a hidden, rarely
   switching 2-state chain as the hard instance, which is the regime of Paper C1. For age-weighted
   estimators this becomes a Chebyshev-type approximation problem for Laplace transforms (PL2
   Section 4, item 2).
5. **Smaller items.** (LD) and (LD2) for the geometric-number-of-cycles design, the continuous-time
   M/G/1 version (Denisov-Shneer 2010 gives the first-order local law, but no difference bounds, so
   (LD) and (LD2) would be new there too), log-convexity of total-progeny laws for E6, and a
   simulation study of the rates.

The project paper should cite F for the exposure law and keep all estimator theory out of it (PL1
Section 3, item 3). Getting F on arXiv first is what makes this possible.

---

## 9. Reading list and corrections

### 9.1 Sources to read before writing

**Still unread, blocking for G'.**

| Source | Why | Status now |
|---|---|---|
| Mitov, Yanev, Adv. Appl. Probab. 33 (2001) 896-911 | possible alternating-renewal version of Dom-D(a), and possibly end behaviour | abstract, keywords and reference list only. Paywalled, no preprint found. Now judged less likely to contain Dom-D(a) (N07u Section 3). Request by interlibrary loan |

**Read since the last version.**

| Source | Finding |
|---|---|
| Denisov, Shneer, Queueing Syst. 64 (2010) 383-393 | read in full. Continuous-time local busy-period law, Cor. 2.1, 2.2. Q1 is its slotted analogue. Q2 and Claim A are not in it (no difference statement of any kind). Its arXiv companion 0712.0728 is a different paper (first-passage tails, cited in PL1) (N07u Section 1) |
| Lamperti, Trans. AMS 88 (1958) 380-387 | read in full. 2 sojourn laws and unequal weights allowed. Distributional only. In the dominated case only N_n/n -> 1, no scaled limit. No shape remark, so nothing to credit for Sh-C (N07u Section 2) |
| Horii-Lefevere-Nemoto 2021, Horii's thesis (Universite Paris Cite, 2022), Horii-Lefevere-Itami-Nemoto PRE 2022 | no follow-up proves their eq. (37), but it follows from Nagaev and Denisov-Dieker-Shneer 2008. Do not quote as open (N07u Section 4) |
| Berger, arXiv 1706.07924v4, Thms 2.3, 2.4, (2.10), (3.6) | checked directly in X11 |
| Kortchemski arXiv 1205.3145v4 eq. (14), Janson arXiv 1112.0510v1 Rem. 18.34 | checked in X12 (arXiv versions only) |

**Checks of detail before citing (not blocking).**

| Source | Why | Status now |
|---|---|---|
| Erickson, Trans. AMS 151 (1970) 263-291 | theorem number for u(n) ~ 1/mu(n) at alpha = 1 | read only through Berger (3.6). Needed only for the later alpha = 1 note |
| Darling, Kac, Trans. AMS 84 (1957) | Mittag-Leffler limit, credit for the mixed case of Dom-D(a) | not opened |
| Yamato, arXiv 2605.23659, Thm 5.8, Rem. 5.10, 5.12 | the strongest known source for Dom-D(a). Confirm the gap to strict alternation and discrete time | read for statements |
| Barbe, McCormick, Mem. AMS 197 (2009) no. 922, Thm 2.3.1 | credit for the difference big-jump lemma in F | theorems not read |
| Cline, Hsing (and Nagaev) | the uniform one-big-jump estimate of repair D | not yet chosen |
| Heath-Resnick-Samorodnitsky 1998, Taqqu-Willinger-Sherman 1997, Mikosch-Resnick-Rootzen-Stegeman 2002 | before writing any sentence on what the on/off literature does not give | abstracts only |
| Lefevere-Mariani-Zambotti, SPA 2011 | before citing it for more than heavy-tailed renewal LD | abstract only |
| Margolin, Barkai, JSP 122 (2006), journal version | whether it derives 0.5946 | arXiv version only |
| Published numbering of Kortchemski AIHP 2015 eq. (14) and Janson Probab. Surveys 2012 Rem. 18.34 | X12 checked arXiv versions | not checked |
| Doney 1989 | F cites it | first page only |

Already read and still valid: Cenac-Le Ny-de Loynes-Offret 2019 Section 4.3, Akimoto-Sera-Yamato-Yano
2020 with supplement, BBDG 1999, Godreche-Luck 2001 Sections 7 and 10, Sera 2024, Plaud-Benichou
2025, Bel-Barkai 2006, Asmussen-Foss-Korshunov 2003.

### 9.2 Corrections owed to the current texts

**Paper F.**
1. Credit Barbe-McCormick for the difference big-jump lemma at `sec_shape.tex:1117` and
   `sec_intro.tex:308`. Partly known, not known. What is new is uniformity in m >= 1 on L >= K a(m) in
   the lattice setting (PL2 Section 1).
2. Add (SPAN) to the hypothesis list for the mode count in the abstract and to the sentence on laws
   without runs of length 1 (`problem131_levy.tex:57`, `:61`, `sec_intro.tex:206-207`).
3. "The whole sign pattern of the first differences is fixed" (`sec_intro.tex:199`). The order of the
   sign changes is fixed, the block lengths are not.
4. Potter bound at `sec_modeproofs.tex:318`, used again at 342-344, cited for y <= 1 but stated for
   y >= 1.
5. K_0 in `thm:mode-count` depends on the run laws and on eta, eta', which are fixed by the laws
   (`sec_shape.tex:923`, `sec_modeproofs.tex:889`).
6. Update the citation of Paper D to its current title and arXiv number.
7. Add Starreveld-Bekker-Mandjes, Doney 1997, Akimoto-Sera-Yamato-Yano and the on/off papers to the
   related work (N05). Cite Mitov-Yanev only generically until read.
8. Do not repeat Starreveld et al.'s sentence that large deviations of occupation times are unstudied.
9. Do not quote Horii-Lefevere-Nemoto's eq. (37) as open.
10. Replace the sentence that leaves infinite means "to a later paper" by a citation of G'.

**Paper G (for G').**
1. "We give the threshold in closed form" (`sec_intro.tex`, Section "The shape"). The equation
   alpha_c = cos(pi alpha_c/2) and the curvature argument at 1/2 are in Baldassarri et al. 1999 and
   Godreche-Luck 2001, eq. (7.6) ff. Claim only the exact count, and now the full classification Sh-C
   for every b, which replaces `thm:shape` and settles `rem:unequal` (N07 Claim 4, X10 Section 1).
   This also affects the abstract, which says "threshold 0.5946...".
2. `conj:count` is false as stated (oscillating initial runs). Replace it by Sh-A with (LR), (LD2),
   (DSRT), the difference condition (S) and nondegenerate critical points (H6). Say that the
   disproof is by exact counts to N = 3000 and becomes complete with Sh-B (N06 Section 4, X10
   Section 3).
3. "Leaves the local law and the end layers unchanged" (`sec_intro.tex:132`). The end layer of a
   prepared start is the prepared kernel kappa_+(j) = pi_+ u_-(j) + (nu_- * u_-)(j) of
   `eq:kappa-prep`, not u_-(j) (PL2 Section 3).
4. "Aperiodic" should be (SPAN), in the statement of `thm:local` and the abstract.
5. Credit Godreche-Luck Section 7 and Wang-Schulz-Deng-Barkai Section VII.A for the end-layer formula.
6. `rem:aging` is now a theorem (Ag-A), under (SRT) in place of (LB). Cite Akimoto-Sera-Yamato-Yano
   2020 for the global aging law.
7. `rem:global` against Lamperti 1958, now read: Lamperti allows 2 sojourn laws and unequal weights,
   his side choice at the regeneration state is i.i.d., so strict alternation needs a one-clause
   reduction, and his dominated case gives only N_n/n -> 1 in probability.
8. Cite F for the finite-mean regime and for the shared identities and lemmas.

**The plans (wording to carry into the papers correctly).**
1. The golden-ratio rule in design language (PL1 Section 3, "exactly when alpha < phi"): 4 corrections
   in Section 8.1. F's own text (`sec_intro.tex`, "The shape") already states the alpha = phi case
   correctly.
2. The start factor is N/(s(alpha-1)) plus a second atom, not N/(alpha-1).
3. PL1 lists "the end layers and their matching under Doney's condition" as passing review. That is
   right, and G' can now add the upper bound of Lemma E under (SRT).
4. The alpha_c closed form is not new (item G1 above).

**The notes (for whoever writes from them).**
1. N01 must say that Dom-D(a) is known, add the one external input of repair D, and record that
   Lamperti 1958 gives only the degenerate limit in the dominated case.
2. N02: the start index s and the mean cycle length s clash in Section 5 (X08 Section 6).
3. N03 (X11 Section 5): replace "O(abs(m - m_*) L_s)" and "jumps of order 1" by o(sigma). Call the
   kernel heuristic and drop M2 as a separate gap. Define eps_N with the de Haan function or as the
   local index, since N T(N)/mu(N) -> (1-alpha)/alpha. Restrict the Lamperti-to-Cauchy expansion to
   abs(t - beta/alpha) = o(1) and state the matching as a parameter identification. Prop C needs only
   regularly varying T_+. Recompute the N/(4 mu(j*)) column with mu = H_{j+1} - 1.
4. N04: E[nu] = 1/(1-rho) in place of E[B] in the Q1 paragraph, with De Meyer-Teugels and Zwart for
   the global form and Denisov-Shneer Cor. 2.1, 2.2 for the local form. Replace "read Denisov-Shneer
   before claiming anything about M/G/1" by the finding of N07u. Restrict E1 for a random-time start
   with alpha < phi to 1 <= k < N. Cite `thm:bigjump`(b) in E2. Mark Claim A and Q3 as proved.
5. N05 line 129 and the HLN row: the follow-up is the 2022 thesis, it does not prove (37), and (37)
   with a = 1 follows from Nagaev and Denisov-Dieker-Shneer.
6. N06 Section 9: the refutation of `conj:count` is conditional on Sh-B (X10). N06 table: "proved
   modulo L*" holds for fresh and fair starts only.
7. N07: remove Lamperti 1958 and Denisov-Shneer 2010 from the "Not reachable" list at the top, keep
   Mitov-Yanev.

**The series README.** RM describes Papers A to F and says that the infinite-mean case "is left to a
later paper". It has no section on Paper G. It should describe F and G' as the closing pair, F for
finite means and G' for infinite means, with G' replacing the current G.

---

## 10. Order of work and odds

### 10.1 Order

1. **Week 1. F corrections and reframe.** The corrections of 9.2 to F, the new introduction and
   positioning. Request Mitov-Yanev by interlibrary loan the same week.
2. **Week 2. F aging.** Close Ag-C(d) in 3 steps, write the aging section, get the golden ratio under
   aging checked.
3. **Week 3. F exposure.** Write the exposure section with the E1 restriction, the E2 citation and the
   credits.
4. **Week 4. F builds.** Journal and arXiv builds, outside read if possible, arXiv posting and EJP
   submission.
5. **Weeks 5 to 6. G' corrections and dominated regime.** The corrections of 9.2 to G, Dom-D with
   repairs A to F and Lemma Q as its own lemma.
6. **Week 7. G' aging.** Ag-A with the epsilon fix, Ag-B with the typo fixed, Ag-B'.
7. **Weeks 8 to 9. L* and Sh-C.** Write L* (Theorem L complete for fresh and fair starts) and Sh-C in
   full.
8. **Weeks 10 to 14. Sh-B.** Decide at week 12: if the one-giant-run range at second order is not
   under control, state the count for alpha < 1 as conditional on Sh-B and move on.
9. **G' builds** with the phase diagram figure, Mitov-Yanev read, then arXiv and EJP or Bernoulli.
10. **After both submissions.** The alpha = 1 note (Theorem A and Prop C, after reading Erickson),
    Claim K, EN1 and EN2, alpha_- = 1/2, the open aging items (M-U, M-nec, M-match).

With this order F goes out in about 4 weeks, and G' about 6 weeks later without Sh-B or about 10 to
11 weeks later with it.

### 10.2 Odds (our judgment)

| Package | Venue | Eventual acceptance |
|---|---|---|
| F (current F + Ag-C + exposure + reframe) | EJP | about 70% |
| G' without Sh-B (count conditional) | EJP or Bernoulli | about 68% |
| G' with Sh-B | EJP or Bernoulli | about 70 to 72% |
| For comparison: one merged paper | EJP | about 75 to 80% before the length penalty, 72 to 77% after |

2 papers at about 70% each give about 1.4 expected acceptances against at most 1 for the merge, and
the 2 outcomes are close to independent, since the main risk for each is a referee's view of its own
regime. An outside read by a probabilist adds a few points to any row.
