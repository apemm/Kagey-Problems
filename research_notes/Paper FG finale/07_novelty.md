# 07. Novelty audit for the merged paper (F plus G)

Date: 2026-10-26. This note checks seven claims of the planned merged paper against the
literature. It builds on `05_literature.md` (same day) and does not repeat what is there unless
the verdict depends on it.

## Reading status key

- FULL: arXiv full text read for the parts named (statements, the relevant section, the
  introduction). Proofs were read only where noted.
- PART: abstract plus the sections named.
- ABSTRACT: abstract, journal record or search snippet only, or known only from how another paper
  quotes it.
- NOT OPENED: title or citation only.

## Search scope (all claims)

- alphaXiv full-text index: semantic searches on "local limit theorem occupation time arcsine",
  "Lamperti distribution asymmetry shape U W", "occupation time unequal indices", "aging
  occupation time".
- Web search (standard and extended): queries on the Lamperti density with an asymmetry parameter
  and its modes; "0.7365" / "alpha = sin(pi alpha)"; Mitov-Yanev 2001; local limit theorems for
  persistent random walks, Levy walks and alternating renewal processes; mode counts of
  occupation-time laws; heavy-tailed switchback and regenerative designs.
- Papers read for this note (FULL or PART): Baldassarri-Bouchaud-Dornic-Godreche
  cond-mat/9805212; Godreche-Luck cond-mat/0010428 (Sections 1, 7, 10); Bel-Barkai
  cond-mat/0506338; Rebenshtok-Barkai 0803.2354; James 0708.0618 (Sections 1, 2.2, 5);
  Sibisi-Sibisi 2609.22952; Wang-Schulz-Deng-Barkai 1809.05856 (Sections V, VII); Cenac-Le
  Ny-de Loynes-Offret 1612.00238 (Sections 2-4, 6); Yamato 2605.23659 (Sections 1, 5, 6);
  Sera 2403.02658 (Sections 1, 3); Melbourne-Pene-Terhesiu 2610.15720 (Sections 1, 2, 6);
  Wang-Chen-Deng 1906.03023; Plaud-Benichou 2510.25859 (main text, SM Sections III-IV).
- Not reachable: Mitov-Yanev 2001 full text (JSTOR; the encyclopedia PDF by Mitov returned 502),
  Lamperti 1958 full text, Darling-Kac 1957, Kasahara's occupation-time papers, Sera 2020,
  Denisov-Shneer 2010. Verdicts that lean on these say so.

The search is bounded. "Not found" means not found in this scope, not that it does not exist.

---

## Claim 1. Local limit theorems for A_N in each regime

### 1a. Finite means (stable local law, F Thm bulk). Verdict: PARTLY KNOWN.

- Doney, A bivariate local limit theorem, J. Multivariate Anal. 36 (1991) 95-102 (ABSTRACT;
  already in F). With the fresh-plus identity it gives the local law at one point at the stable
  scale.
- Berger, PTRF 175 (2019), Thm 3.3 (ABSTRACT; in F). F's own introduction says this gives the
  window |k - pN| <= K B_N.
- Melbourne, Pene, Terhesiu, arXiv 2610.15720 (PART). Theorem 6.1 is a mixing local limit
  theorem for Z-valued observables on Young towers, at a fixed point q of the stable scale, under
  the invariant measure, with test sets A, B in the tower. Theorem 1.2 is the example with an
  observable taking different values near two neutral fixed points of equal exponent, which is
  the dynamical version of an occupation count. Their nondegeneracy condition (Definition 3.2,
  the spanning condition on (v(x_i), 1)) needs both heavy components at the same index. So
  unequal indices are outside their theorem.
- What is not in these sources: uniformity over all k, the fresh and general starts, unequal
  scales (B_N = max of the two scales), and the big-jump zone. F's introduction already states
  this division correctly.
- Credit and claim: cite Doney 1991, Berger 2019 and MPT 2026 for the local law at the stable
  scale, and claim the uniform-in-k statement, the initial runs and unequal scales.

### 1b. Balanced infinite means (local Lamperti law, and its equivalence with SRT, G Thm 1). Verdict: NOT FOUND.

- Global law: Lamperti 1958 (ABSTRACT; classical). Integrated moderate deviations near the
  endpoint: Sera, arXiv 2403.02658 (FULL statements), Thm 3.13 and Remark 3.14,
  mu(S^{A_1}_n / n <= c(n)) ~ (beta_2/beta_1)(sin pi alpha/(pi alpha)) c(n)^alpha for c(n) -> 0
  and n c(n) -> infinity, for infinite ergodic transformations with one index. This is a
  cumulative statement near the end of the Lamperti law, not a point probability.
- Conditional ("tied-down") distributional laws: Aaronson-Sera arXiv 2308.09406 and Sera-Yano
  TAMS 2019 (ABSTRACT). These condition on a return at time n and stay distributional.
- No source found states N P(A_N = k) -> L(k/N), or ties a local occupation law to the strong
  renewal theorem. The SRT criterion itself is Caravenna-Doney (EJP 2019), as G says.
- Credit and claim: cite Lamperti for the density, Caravenna-Doney for the SRT criterion, and Sera
  2024 as the closest integrated endpoint estimate. The local law and the equivalence can be
  claimed as new within this search.

### 1c. Dominated regime (01_phase_diagram.md, Theorem D(b)-(d)). Verdict: NOT FOUND (local part).

- The global part (a) is known. See Claim 2.
- No local statement found: neither D_N P_N(N - j) -> rho(j/D_N), nor the condition (SRT_-) plus
  (W_+), nor the end-layer matching. Cenac et al. (1612.00238, Section 4.3) and Yamato
  (2605.23659, Thm 5.8) are distributional. Wang-Chen-Deng (1906.03023, FULL) treat a two-state
  process with alpha_+ != alpha_- but give only mean squared displacements and the long-time state
  fractions.
- Credit and claim: claim (b)-(d) as new. State (a) as known with the sources of Claim 2.

---

## Claim 2. The global limit in the dominated regime. Verdict: KNOWN (in distribution), with one routine gap.

Sources, in order of strength:

1. **Yamato, State-dependent inverse-subordinator time changes of regenerative processes,
   arXiv 2605.23659 (May 2026), FULL Sections 1, 5, 6.** Theorem 5.8 is a multiscale joint
   limit for the occupation times of excursion classes. The dominant classes (heaviest index
   alpha) give generalized arcsine laws. A sub-dominant class with index alpha~_i in [alpha, 1)
   gives O^{(i)}(lambda t)/g_i(h(lambda)) -> xi~^{(i)}(S^{-1}(t)): a stable subordinator of the
   lighter index evaluated at the inverse of the dominant subordinator. Remark 5.12(ii) gives the
   marginal E exp(-q Phi(t)) = E_alpha(-beta~ q^{alpha~} t^alpha). Remark 5.10 treats the endpoint
   alpha~ = 1 (relatively stable, for instance finite mean), where the limit is
   beta~ S^{-1}(t), a dilated Mittag-Leffler variable, which he calls the Darling-Kac case. In
   01's notation these are exactly Y = S_-(E) (alpha_- < 1) and mu_- E (mu_- finite).
2. **Cenac, Le Ny, de Loynes, Offret, Persistent random walks II, J. Theoret. Probab. 32 (2019)
   633-658, arXiv 1612.00238, FULL Section 4.3.** This is the lattice walk S_n = 2A_n - n itself.
   For the "extremal mean drift" case (one side dominates) they write that the limit "seems to be"
   (u^{1 - alpha/gamma}/Xi(u))(S_{[ut]}/u - t) => T^d_gamma(N^u_alpha(t)) when the lighter time is
   in D(gamma) with gamma <= alpha < 1, and
   (u^{1-alpha}/Xi(u))(S_{ut}/u - t) => N^u_alpha(t) (a Mittag-Leffler local time) when it is
   relatively stable. They add that the next term for gamma in [1, 2] is "heuristically"
   S^d_gamma(N_alpha(t))/u^{alpha/gamma}. This is stated without proof. F already cites this
   paper, but for other results.
3. **Darling-Kac (TAMS 84, 1957), NOT OPENED.** This is the classical Mittag-Leffler limit for the
   time spent in a set of finite measure. The mixed case alpha_+ < 1 < alpha_- is an instance once
   the minus runs are read as that set. Sera 2403.02658, Remark 3.10, quotes the general form.
4. **Lamperti 1958 (ABSTRACT).** His theorem covers every b in [0, infinity] for the fraction
   A_N/N. For b in {0, infinity} the limit is degenerate, so he does not give the scaled limit of
   N - A_N. G and 01 say the same.
5. **Mitov-Yanev, Adv. Appl. Probab. 33 (2001) 896-911 (ABSTRACT).** Limit theorems for the
   occupation-time process of alternating renewal processes with infinite-mean cycles; extends
   Dynkin, Lamperti and Erickson; "some new phenomena". I could not read it. It may well contain
   the scaled lighter-side limit for unequal indices. **Read it before the merged paper goes
   out.**
6. **Rebenshtok-Barkai, 0803.2354 (FULL Section V.B).** For unequal indices they state that in the
   long-time limit the system occupies only the states with the smallest alpha. That is the
   degenerate first-order statement, at physics level.

The gap: Yamato's excursion classes are chosen by a Poisson marking, not by strict alternation,
and his time is continuous. The alternating lattice model is not literally a special case. The
same proof gives it, because the counts of plus and minus runs differ by at most one, so this is
routine. Cenac et al. treat the right model but give no proof.

Credit and claim: state Theorem D(a) as known. Cite Yamato 2026 (Thm 5.8, Rem. 5.10, 5.12),
Darling-Kac for the mixed case, Cenac et al. 2019 Section 4.3 for the lattice walk (stated there
without proof), and Mitov-Yanev 2001 after reading it. Claim only the local statements and the
explicit density rho (for equal indices with b = 0, the ratio density of S/S', which is classical:
Lamperti 1958, Zolotarev, Chaumont-Yor 4.23.3, James 2010 eq. (1.1)).

---

## Claim 3. Big-jump local asymptotics and the boundary layer (F Thm B kernel). Verdict: PARTLY KNOWN.

- **Wang-Schulz-Deng-Barkai, PRE 98 (2018) 042139, arXiv 1809.05856, FULL Section VII.**
  - VII.B, eq. (83), for 1 < alpha < 2, one interval law for both states and a fair start: the
    non-normalized density of epsilon = T_+ - t/2 is
    (alpha b_alpha/(t^alpha |Gamma(1-alpha)|)) chi(2|epsilon|/t) with
    chi(z) = z^{-1-alpha}(1 - (alpha-1)z/alpha) on (0, 1]. It depends only on alpha and b_alpha.
    This is the continuum, symmetric shape of F's interior kernel.
  - VII.A, eqs. (74)-(77), for alpha < 1: near the endpoint,
    f_{T+}(t, T+) ~ p_0(t) L^{-1}[-1/2 + 1/(1 - phi^(u))]. That is the survival probability times
    (an atom plus the renewal density) in continuous time. It is the formal analogue of G's end
    layer T(N) u(j).
  - Simulations only. No error terms, no lattice statement, no unequal laws, and the authors leave
    "the connection with the big jump principle" and "the effect of initial preparation on the rare
    fluctuations" to future work (Section VIII).
- **Rebenshtok-Denisov-Hanggi-Barkai 2014; Schulz-Barkai 2015; Vezzani-Barkai-Burioni 2019,
  2020** (in F; not re-read here). F's introduction already credits the Levy-walk infinite density
  |v|^{-1-alpha}[alpha - (alpha-1)|v|], the matching to the stable bulk, and the big-jump
  derivation.
- **Godreche-Luck 2001 (FULL Sections 7, 10).** For alpha < 1, eq. (7.11): a scaling form near
  M = 1 with a non-universal scaling function h(z). For 1 < alpha < 2: the stable typical law and
  bifractal moments (7.13). No kernel.
- Rigorous inputs (in F): Denisov-Dieker-Shneer 2008, Berger 2019 PTRF Thm 2.4, Berger-Birkner-Yuan
  2024. These are local big-jump laws for sums with a fixed number of terms, not for the count at a
  fixed time.
- Not found: the lattice two-term kernel gamma(N-k) f_+(L_k) + T_+(L_k) u_-(N-k) with uniform
  errors up to the endpoint, the run in progress at N as a separate term, the boundary-layer
  constants kappa(j), unequal laws, and the dominated-regime kernel of 01 Claim K.
- Credit and claim: say that the continuum shape of the interior kernel is known formally (WSDB
  eq. (83), RDHB 2014), and so is the endpoint structure for alpha < 1 (WSDB eqs. (74)-(77)).
  Claim the lattice theorem: uniform errors, the boundary layer, both laws, and the initial run.

---

## Claim 4. The bulk shape with unequal weights (06_shape.md, Theorem C). Verdict: PARTLY KNOWN (b = 1 threshold known; b != 1 not found).

What is known:

- **Baldassarri, Bouchaud, Dornic, Godreche, PRE 59 (1999) R20, arXiv cond-mat/9805212 (FULL;
  4 pages).** Same law for both states and Levy-stable intervals. Eq. (8) is the magnetization
  density. The text says: "For theta < theta_c = 0.5946..., where theta_c is the solution of
  theta_c = cos(pi theta_c/2), x = 0 corresponds to a minimum of f(x), while for larger theta, it
  corresponds to a local maximum." They mention unequal scale factors for the two states ("the
  distribution f(x) becomes asymmetrical") but study only the persistence exponents there, not the
  shape.
- **Godreche-Luck, JSP 104 (2001) 489, Section 7 (FULL).** Expansion of f_M near x = 0 with the
  coefficient (cos^2(pi alpha/2) - alpha^2)/cos^2(pi alpha/2). "x = 0 is a minimum ... for
  alpha < alpha_c, while it is a maximum for alpha > alpha_c, with alpha_c = cos(pi alpha_c/2),
  yielding alpha_c = 0.594611 [24]." Section 10: "a U-shaped curve for alpha < alpha_c ..., while
  its maximum is at zero, for alpha > alpha_c." This is symmetric (one law, averaged initial sign).
- **Rebenshtok-Barkai, J. Stat. Phys. (2008), arXiv 0803.2354 (FULL).** Eq. (23) is the Lamperti
  density with asymmetry R. Section IV.C gives alpha_c = 0.59461 for the symmetric two-state limit
  (their eq. (45)). They do not analyze the shape in R.
- **Bel-Barkai, PRE 73 (2006) 016125, arXiv cond-mat/0506338 (FULL).** Eq. (6) is the Lamperti
  density with R_x = P_x/(1 - P_x). Figures 2-4: U shape at alpha = 0.3 and 0.5, and a distorted
  W shape at alpha = 0.8 with R != 1 (simulation plus formula). The abstract says the occupation
  time "approaches U or W shaped distributions". No threshold in R.
- **Margolin-Barkai 2006 and Zaburdaev-Denisov-Klafter 2015** (in G): the symmetric value only.
- **James, Lamperti-type laws, AAP 20 (2010), arXiv 0708.0618 (PART).** Densities, cdf (2.12),
  mixture representations, the skewed-Bessel occupation law (Prop. 5.1). No discussion of modes.
- **Sibisi-Sibisi arXiv 2609.22952 (FULL; 12 pages).** Representation-free densities of stable
  ratios, the Lamperti density for general z. Nothing on modes.
- **Lamperti 1958: NOT OPENED.** I could not check whether he discusses the shape. James and
  Sibisi-Sibisi describe his paper as deriving the density by Stieltjes inversion, and neither
  mentions a shape analysis.

What was not found:

- the count "exactly 1 or 3 critical points" for b != 1;
- the window |log b| < beta_c(alpha) with beta_c in closed form;
- the second constant alpha_1 = 0.7365 (alpha = sin pi alpha), beyond which every b gives W;
- the degenerate cases;
- the mode criterion alpha > sin(pi alpha) for the ratio density K_alpha of S/S'.

**Correction for G (important).** G's introduction says "We give the threshold in closed form",
and G Section shape says the arXiv version of Margolin-Barkai has the value but no derivation.
The closed-form equation alpha_c = cos(pi alpha_c/2) and the local-curvature argument at x = 1/2
are in Baldassarri et al. 1998/1999 and in Godreche-Luck 2001 eq. (7.6) ff. G already cites
Godreche-Luck, but not for this. What G adds for b = 1 is the proof that there are exactly 1 or 3
critical points: those papers check only the sign of the curvature at 1/2. The merged paper must
credit Baldassarri et al. and Godreche-Luck for alpha_c and its equation, and claim only the exact
count.

Bel-Barkai's alpha = 0.8, R != 1 W shape agrees with Theorem C (0.8 > alpha_1, so W for every b).
That is worth a sentence.

Credit and claim: the threshold alpha_c, its defining equation and the U/W change at b = 1 are
due to Baldassarri-Bouchaud-Dornic-Godreche (1998/99) and Godreche-Luck (2001). The asymmetric W
shape was seen numerically by Bel-Barkai (2006). The merged paper can claim the exact critical-point
count for all (alpha, b), beta_c(alpha) in closed form, alpha_1, and the degenerate cases.

---

## Claim 5. Exact mode counts of the law of A_N. Verdict: NOT FOUND.

- No source found counts the local maxima of P(A_N = k) at finite N, or relates them to end
  profiles. Searches on mode counts of occupation-time and Levy-walk laws returned only the
  continuum U/W discussion (Claim 4) and the physics golden-ratio exponent that F already credits
  (Wang-Li-Hanggi 2016; Cipriani-Denisov-Politi 2005; Lee-Dadswell-Nickel-Gray 2005).
- Ingredients that are known: the bell shape of stable densities (Kwasnicki 2020, in F) and the
  U/W threshold of the limit density at b = 1 (Claim 4).
- Credit and claim: claim the eventual counts in both regimes, crediting Kwasnicki and the U/W
  literature for the limit shapes. The every-N statements stay conjectures.

---

## Claim 6. Heavy-tailed regenerative switchback designs and exposure laws (04_exposure_queues.md). Verdict: NOT FOUND (design side); the cycle asymptotic is KNOWN.

- Design papers already read in 04 (arXiv full text): Bojinov-Simchi-Levi-Zhao; Hu-Wager;
  Glynn-Johari-Rasouli; Li-Johari-Kuang-Wager (regenerative switchbacks in a bounded queue,
  App. A.3.1, light-tailed cycles); Jia-Kallus-Yu; Hu 2609.13698 (random-duration runs of finite
  mean). The extra web search on heavy tails, busy periods and exposure imbalance found practitioner
  notes and an arXiv appendix (2602.23257, ABSTRACT) that mentions heavy-tailed disturbances in
  randomization inference, but nothing on infinite-variance cycles or exposure counts.
- Known: (LR) for the cycle. Kortchemski AIHP 2015 eq. (14) and Janson Probab. Surveys 2012
  Remark 18.34, read as Galton-Watson total progeny (as recorded in 04). Denisov-Shneer, Queueing
  Syst. 2010 (NOT OPENED) may hold the continuous-time local busy-period result.
- Credit and claim: credit Kortchemski and Janson (and Denisov-Shneer, after reading it) for the
  cycle law. Claim the exposure corollaries (scale N^{1/alpha}, the severe-imbalance asymptotic,
  the start factor, the golden-ratio rule) as applications of F, and say plainly that the design
  literature found assumes light-tailed cycles.

---

## Claim 7. Local aging laws (02_aging.md). Verdict: global KNOWN (physics-level proof); local NOT FOUND.

- **Akimoto-Sera-Yamato-Yano, PRE 102 (2020) 032103, arXiv 2004.00808** (FULL in 02). Thm 2 is
  the aged generalized arcsine law for two-state renewal processes with 0 < alpha < 1. The
  supplement proof is a scaling argument; convergence to the scaling limit is asserted. The aged
  density is 02's L_theta, and the atoms are q^{+-}(r).
- **Akimoto, PRE 108 (2023) 054113, arXiv 2306.00359** (PART, in 02 and F). Triple Laplace
  transform of the aged occupation time and moments. For 1 < alpha < 2 only the equilibrium start.
- **Plaud-Benichou, arXiv 2510.25859 (FULL main text).** Aged occupation law for discrete-time
  jump processes (not renewal), with edge Dirac masses. They credit the renewal case to
  Godreche-Luck (two-time correlator) and Akimoto et al. (aged law). Distributional.
- **Wang-Chen-Deng, arXiv 1906.03023 (FULL).** Aging two-state process with alpha_+, alpha_- in
  (0,2): mean squared displacements only.
- **Barkai-Cheng, J. Chem. Phys. 118 (2003) 6167; Schulz-Barkai-Metzler PRX 2014;
  Godreche-Luck 2001 Section 8** (NOT OPENED beyond Godreche-Luck Section 10): aging of the
  number of renewals and of correlations. Distributional.
- **Wang-Vezzani-Burioni-Barkai 2019** (in F): ordinary versus equilibrated start for 1 < alpha < 2.
- Not found: the local aged law N P_N(xN) -> L_theta(x), the lattice atoms and end layers with the
  constant c_+(theta), the closing of G's aging conjecture, and aging at theta N for 1 < alpha < 2
  (the aged atom of order N T(N), the extra kernel terms).
- Credit and claim: cite ASYY 2020 Thm 2 for the global aged law (calling its proof physics-level is
  accurate; say "the convergence to the scaling limit is asserted there") and Akimoto 2023. Claim the
  local law, the ends, the finite-mean aging terms, and the proof of the global law under (RV) as a
  by-product (02, Remark 2 of Section 4.4).

---

## Summary table

| # | Claim | Verdict | Key sources |
|---|---|---|---|
| 1a | Local law, finite means | PARTLY KNOWN | Doney 1991; Berger 2019; Melbourne-Pene-Terhesiu 2026 (one point, stationary, equal index) |
| 1b | Local Lamperti law, equivalence with SRT | NOT FOUND | Sera 2024 (integrated endpoint), Caravenna-Doney 2019 (SRT criterion) |
| 1c | Local law, dominated regime | NOT FOUND | (global part: Claim 2) |
| 2 | Global limit, dominated regime | KNOWN in distribution | Yamato 2026 Thm 5.8; Darling-Kac 1957; Cenac et al. 2019 Sec. 4.3 (no proof); Mitov-Yanev 2001 (unread) |
| 3 | Big-jump kernel and boundary layer | PARTLY KNOWN (formal, continuum, symmetric) | WSDB 2018 eqs. (74)-(77), (83); RDHB 2014; VBB 2019 |
| 4 | Shape of L_{alpha,b} | PARTLY KNOWN: b = 1 threshold known; b != 1 not found | BBDG 1998/99; Godreche-Luck 2001 Sec. 7; Bel-Barkai 2006 (numerical W at alpha = 0.8) |
| 5 | Exact mode counts | NOT FOUND | Kwasnicki 2020 (bell shape) as input |
| 6 | Heavy-tailed switchbacks | NOT FOUND (design); cycle (LR) KNOWN | Kortchemski 2015; Janson 2012 |
| 7 | Local aging | global KNOWN (physics-level proof), local NOT FOUND | ASYY 2020 Thm 2; Akimoto 2023 |

## Actions for the merged paper

1. Rewrite G's claim "we give the threshold in closed form". Credit Baldassarri et al. (PRE 59,
   R20, 1999) and Godreche-Luck (2001, eq. (7.6) ff.) for alpha_c = cos(pi alpha_c/2), and claim
   only the exact count.
2. State Theorem D(a) as known (Yamato 2026; Darling-Kac; Cenac et al. Section 4.3).
3. Read Mitov-Yanev 2001 (Adv. Appl. Probab. 33, 896-911) before submission. It is the most likely
   place for an alternating-renewal version of D(a).
4. Read Lamperti 1958 for any remark on the shape of the density.
5. Read Denisov-Shneer 2010 before writing anything about M/G/1 busy periods.
6. Add Bel-Barkai 2006 as the numerical precedent for the asymmetric W shape.

---

## Update after reading the originals

Date: 2026-10-26 (same day, second pass). Four sources were chased. Reading status uses the key
at the top of this note.

### What was read

| Source | Status | Where |
|---|---|---|
| Denisov-Shneer, Queueing Syst. 64 (2010) 383-393, DOI 10.1007/s11134-010-9167-0 | FULL (all 11 pages, proofs included) | Open-access PDF from Springer. No arXiv version exists; arXiv 0712.0728 is their other paper (first-passage times, cited in PL1) |
| Lamperti, Trans. AMS 88 (1958) 380-387 | FULL (all 8 pages, proofs included) | Free PDF on ams.org |
| Mitov-Yanev, Adv. Appl. Probab. 33 (2001) 896-911 | ABSTRACT, keywords and reference list only | Paywalled on Cambridge Core (purchase "temporarily unavailable"); no preprint or author copy found; the Mitov encyclopedia PDF returned 502 again |
| Horii-Lefevere-Nemoto, arXiv 2106.03182 | FULL (re-read Sections 1-2 and 4.2) | arXiv |
| Horii PhD thesis, Universite Paris Cite, approved 2022-07-07, DOI 10.70675/e62613eaz118cz4f85zbfedz421219b44c54 | ABSTRACT (full French abstract from the Crossref record) | Full text not opened |
| Horii-Lefevere-Itami-Nemoto, PRE 106 (2022) 034130, arXiv 2203.08584 | FULL | arXiv |

### 1. Denisov-Shneer 2010: what it proves

Setting: continuous-time M/G/1 (Poisson arrivals, rate lambda), rho = E B/E A < 1, busy period
tau = B_1 + ... + B_nu, where nu is the number served.

- **Thm 2.1** (B absolutely continuous): P(nu = n) = f_{S_n}(0)/n with S_n = sum (B_i - A_i), and
  f_tau(t) = f_{X_t}(0)/t with X_t = sum_{i <= N(t)} B_i - t. This is the continuous analogue of
  the cyclic lemma Q0.
- **Thm 2.2** (fixed T, Delta = (0, T], assuming P(B in t + Delta) e^{eps t} -> infinity for every
  eps > 0, i.e. locally heavier than exponential; no density needed):
  P(tau in t + Delta) ~ P(X_t in Delta)/(lambda t) ~ P(X_[t] in Delta)/(lambda [t]).
- **Conditions.** (A): E B < infinity and F(x + Delta) intermediate regularly varying (true when it
  is regularly varying). (B): E B^2 < infinity, a square-root-insensitivity condition and a
  two-big-jumps condition (covers e^{-x^beta}, beta < 1/2, and lognormal-type tails). (A'), (B')
  are the same on the density f_B.
- **Cor. 2.1** ((A) or (B) for some T): P(tau in t + Delta) ~ P(B in (1 - rho)t + Delta).
- **Cor. 2.2** (B absolutely continuous, (A') or (B')): f_tau(t) ~ f_B((1 - rho)t).
- **Thm 3.1** ((A) or (B) with T = infinity): P(tau > t) ~ E[nu] P(B > (1 - rho)t), with
  E nu = 1/(1 - rho). This is De Meyer-Teugels 1980 (M/G/1, regularly varying) and Zwart 2001
  (GI/G/1), reproved briefly.
- Subexponential setting throughout. Lattice B is allowed only in the integro-local form with
  fixed T; under (A) with T below the span the ratio condition fails, so in effect T must be a
  multiple of the span. No integer-time, Bernoulli-arrival or slotted statement, and **no
  difference or second-order local statement** of any kind.

Bearing on 04_exposure_queues.md:
- **Q1.** Not covered literally: the slotted Geo/G/1 cycle is discrete time with Bernoulli
  arrivals, and DS's proof rests on the Poisson formula (3) (Cohen (4.63)). But Cor. 2.2,
  f_tau(t) ~ f_B((1 - rho)t), is the exact continuous-time analogue of f_C(n) ~ f_W((1 - rho)n).
  Q1 stays KNOWN (Kortchemski 2015 eq. (14), Janson 2012 Rem. 18.34, both discrete); add DS 2010
  Cor. 2.2 as the M/G/1 version. The proof routes differ (Poisson mixing in DS; cyclic lemma plus
  a local big jump in Q1).
- **Q2 and Claim A.** Untouched; DS give first-order equivalences only. Verdict stays NOT FOUND.
- **Fix in 04, Lemma Q1 paragraph.** The text says "Zwart's and Denisov-Shneer's
  P(B>t) ~ E[B] P(sigma>(1-rho)t)". In DS the busy period is tau and the factor is E[nu] (mean
  number served, = 1/(1 - rho)), not E[B]. The global form is De Meyer-Teugels/Zwart (reproved by
  DS); the local form to quote is DS Cor. 2.1/2.2.
- **Embedded M/G/1 (04, "Other versions").** DS Thm 2.1 eq. (4) gives P(nu = n) as a density at
  0, but they derive no local asymptotics for nu. The customer-count version is not in DS.

### 2. Lamperti 1958: what it proves

- **Setting.** Discrete-time process (not necessarily Markov), states A, B and one state sigma;
  visits to sigma form a recurrent event, X_0 = sigma, and every passage between A and B goes
  through sigma. N_n = time in A up to n.
- **Two sojourn laws are allowed.** After sigma the process enters A with probability p, B with
  probability q; the excursion laws f^(1), f^(2) are arbitrary and different; F = pF_1 + qF_2 is
  the full recurrence-time law.
- **Theorem 1 (necessary and sufficient).** N_n/n converges in law iff (1.2)
  a = lim E(N_n/n) exists and (1.3) delta = lim_{x->1-} (1 - x)F'(x)/(1 - F(x)) exists. By his
  Thm 2 the latter is 1 - F(x) = (1 - x)^delta L(1/(1 - x)): the combined recurrence time is
  regularly varying of index delta. Nothing is assumed about each side separately beyond the
  existence of a.
- **The limit.** For a, delta not in {0, 1}: density (1.4) with asymmetry k = (1 - a)/a.
  Otherwise (1.5): a = 1 gives mass 1 at 1; a = 0 mass 1 at 0; delta = 1 (e.g. finite mean) mass 1
  at a; delta = 0 the Bernoulli law (mass a at 1, 1 - a at 0).
- **Dominated case.** If the A side is heavier (smaller index), E(N_n/n) -> 1, so a = 1 and
  N_n/n -> 1 in probability. Degenerate; **no scaled limit of n - N_n**. Unequal weights at a
  common index give the nondegenerate law with k != 1.
- **Method.** Moments via double generating functions, Karamata's Tauberian theorem, Stieltjes
  inversion. Distributional only; no local statement.
- **Shape.** No remark on the shape or modes of (1.4). Action item 4 is closed: nothing to credit.
- **Model mismatch.** Strict on/off alternation is not literally his model (his side choice at
  sigma is i.i.d.). The usual reduction (alternating counts differ by at most one; p = q = 1/2
  gives the same limit) is routine; say so in one clause.

### 3. Mitov-Yanev 2001: blocked

- Abstract (Cambridge Core metadata): "The asymptotic behaviour of an occupation-time process
  associated with alternating renewal processes is investigated in the infinite mean cycle case.
  The limit theorems obtained extend some asymptotic results proved by Dynkin (1955), Lamperti
  (1958) and Erickson (1970) for the classical spent lifetime process. Some new phenomena are also
  presented." Keywords: alternating renewal processes, stable laws, spent time, limiting
  distributions.
- **The reference list matters.** The Lamperti paper they cite is J. Math. Mech. 7 (1958), "Some
  limit theorems for stochastic processes" (the spent-lifetime paper), **not** the Trans. AMS
  occupation-time theorem. Dynkin 1955 and Erickson 1970 are also age and strong-renewal results.
- **Companion papers.** Mitov-Yanev, J. Appl. Probab. 38 (2001), "Regenerative processes in the
  infinite mean cycle case" (ABSTRACT): waiting and life periods in stable domains with indices in
  (1/2, 1], using "the spent time distributions of the corresponding alternating renewal process".
  Mitov, Serdica Math. J. 25 (1999) (EuDML abstract): limit theorems for the spent and residual
  work time when at least one of the two means is infinite. Search-result summaries of Mitov's
  encyclopedia entry (page itself unreachable) describe the 2001 AAP paper as deriving the spent
  and residual working-time processes in the infinite-mean case.
- **Inference (not verified).** The "occupation-time process" of MY 2001 is most likely the spent
  working time (age within the current on period, perhaps jointly with the cycle age), not the
  cumulative time on, A_N. The (1/2, 1] range in the companion paper points to Erickson-type
  strong-renewal hypotheses. Whether unequal indices are covered is unknown. The chance that MY
  contains the scaled dominated-regime limit D(a) now looks lower than before, but it is not
  excluded.
- **Action.** Still read it before submission (library access or interlibrary loan). Until then
  cite it only as limit theorems for alternating renewal processes in the infinite-mean case, with
  no claim about what it does or does not cover.

### 4. Horii-Lefevere-Nemoto "open problem": status

- The sentence (Section 4.2, after eq. (37)) concerns the numerically observed form
  log P[N_t < xt] ~ a log M_0(t) + log t + b for fixed x below 1/E tau, with a = 1 for Pareto and
  inverse Rayleigh. The proved results are Thm 2.1/2.2 (MGF, integer Pareto m >= 3).
- **Follow-ups.** OpenAlex lists two citing works: Horii-Lefevere-Itami-Nemoto PRE 2022 (FULL; it
  studies variance scaling and says the earlier paper "did not succeed to translate it to the
  correction term of the LDP") and Akimoto PRE 2023 (alternating-renewal moments, not this
  question). Horii's thesis (2022, ABSTRACT) proves the MGF asymptotic (Ch. 3) and treats the
  finite-time rate function "using numerical simulation". alphaXiv and web searches for 2022-2026
  found no paper proving (37). **No follow-up settles it.**
- **But it is a direct corollary of classical big-jump large deviations** (my own reading; no
  paper found that says so). By their eq. (39), P[N_t < xt] = P(S_{floor(xt)} > t), and the
  deviation t - floor(xt) E tau is linear in t. For a regularly varying tail with finite mean,
  P(S_n - n E tau > y) ~ n P(tau > y) uniformly in y >= c n (A.V. Nagaev 1969 and S.V. Nagaev,
  Ann. Probab. 7 (1979), finite variance; Cline-Hsing 1991 and Denisov-Dieker-Shneer, Ann.
  Probab. 36 (2008), in general, including index in (1, 2)). Hence
  P[N_t < xt] ~ xt P(tau > (1 - x E tau)t): a = 1, and b = log(x (1 - x E tau)^{-(m-1)}) for
  Pareto of tail index m - 1.
  - Check against their Fig. 5: Pareto m = 3 (E tau = 1, x = 1/2) gives b = log 2 = 0.69 against
    the fit a = 1.01, b = 0.92; m = 3.5 (E tau = 2/3) gives b = 0.32 against the fit b = 0.43.
    Both agree within the slack of a two-parameter fit.
  - Lognormal also lies in the big-jump domain at linear deviations (DDS 2008), so a = 1 is
    expected there too; their fitted a = 0.89 is a finite-t effect.
- **Verdict.** Quote the sentence only as what HLN wrote in 2021, **not** as a current open
  problem. If it is mentioned at all, say the observed asymptotic follows from Nagaev's theorem
  (and DDS 2008), or leave it out. Calling it open would invite a referee to point out the
  classical answer.

### Verdict changes

| # | Claim | Old verdict | New verdict | Reason |
|---|---|---|---|---|
| 2 | Global limit, dominated regime | KNOWN in distribution; Lamperti ABSTRACT; MY unread | Unchanged (KNOWN in distribution). Lamperti part now FULL: unequal laws and weights allowed; dominated case gives only N_n/n -> 1 (or 0) in probability, no scaled limit. MY still unread, now judged less likely to contain D(a) (it extends spent-lifetime results) | Lamperti read in full; MY reference list |
| 4 | Shape of L_{alpha,b} | Lamperti NOT OPENED for shape | Unchanged (PARTLY KNOWN). Lamperti gives the density only, no shape remark; the BBDG/Godreche-Luck credit stands as the earliest shape analysis found | Lamperti read in full |
| 6 | Cycle law (LR), Q1 | KNOWN (Kortchemski, Janson); DS NOT OPENED | KNOWN, with DS 2010 Cor. 2.2 as the continuous-time M/G/1 local version. The slotted discrete statement itself is not in DS | DS read in full |
| 6 | (LD), (LD2) for the cycle (Q2, Q3, Claim A) | NOT FOUND (DS unread) | NOT FOUND, firmer: DS has no difference statement | DS read in full |
| - | HLN "open problem" | Possibly settled by a follow-up | Not settled by any follow-up, but follows from classical big-jump large deviations (own derivation, Section 4). Do not quote as open | HLN, HLIN, thesis abstract, OpenAlex citations |

### Corrections to make elsewhere

1. 04_exposure_queues.md, Lemma Q1: replace "E[B]" by "E[nu] = 1/(1 - rho)" in the Zwart/DS
   sentence, attribute the global form to De Meyer-Teugels 1980 and Zwart 2001, and add DS 2010
   Cor. 2.2 as the local continuous-time analogue.
2. 04 Section 5 and the finale report's reading list: DS 2010 is read. Replace "read it before
   claiming anything about M/G/1" with: the slotted local law is the discrete analogue of DS
   Cor. 2.2; (LD) and (LD2) are not in DS.
3. Finale report, HLN row of the reading table, and 05_literature.md line 129: the follow-up is
   the 2022 thesis; it does not prove (37); (37) with a = 1 follows from Nagaev/DDS.
4. Remove Lamperti 1958 and Denisov-Shneer 2010 from the "Not reachable" list at the top of this
   note; keep Mitov-Yanev there.
