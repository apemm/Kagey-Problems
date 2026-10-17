# Paper D and the Journal of Theoretical Probability: literature notes

Date: 2026-10-16. Scope: JTP (Springer, ISSN 0894-9840) papers from 2015 to 2026 on random walks with
memory, and recent work close to Paper D (`kagey-problems/problem131/paperD`, "Endpoint crossings for
the elephant random walk", 49 pages as compiled).

## How this was searched

- Crossref: every JTP record from 2015 on (949 records; Crossref coverage of JTP looks incomplete, at about
  70 to 100 records a year), with titles filtered for elephant, memory, reinforced, persistent, coin,
  urn, recursive tree, local limit and so on, and authors filtered for Bercu, Coletti, Gava, Schütz, Baur,
  Bertoin, Takei, Kubota, Miyazaki, Laulin, Guérin, Raschel, Simon, Kiss, Engländer, Volkov, Gut and
  Stadtmüller. Reference lists and received/accepted dates came from Crossref.
- Web search, the arXiv abstract pages and alphaXiv. Springer pages (articles, journal search,
  submission guidelines) redirect to a login and could not be read. So JTP page counts and section
  structure come from the arXiv versions where I could get them.
- Read in full: Engländer–Volkov (arXiv:1606.03281v1, the JTP coin-turning paper) and Althaus–Hartung–Steiner
  (arXiv:2405.04385v1). For the others I read abstracts and reference lists only.

## 1. JTP papers on walks with memory, 2015 to 2026

Only a few JTP papers are on the elephant random walk (ERW) itself. The Bercu, Coletti–Gava–Schütz,
Kubota–Takei, Miyazaki–Takei, Baur, Bertoin and Laulin ERW papers all appeared in other journals
(J. Phys. A, J. Math. Phys., J. Stat. Phys., Trans. AMS, SPA, ECP, EJP, AIHP). None of them is in JTP.

| # | Paper | JTP ref | DOI | Relevance to D |
|---|---|---|---|---|
| 1 | J. Engländer, S. Volkov, *Turning a coin over instead of tossing it* | 31 (2018) 1097–1118 | 10.1007/s10959-016-0725-1 | High. This is the persistent walk with turning probability p_n. At p_n = a/n the frequency of heads tends to Beta(a,a), which is U-shaped for a<1 and humped for a>1, so ends and middle trade places at a=1. |
| 2 | J. Engländer, S. Volkov, *Impatient random walk* | 32 (2019) 2020–2043 | 10.1007/s10959-019-00901-4 | Low. A follow-up on walks with time-inhomogeneous memory. |
| 3 | P. Cénac, A. Le Ny, B. de Loynes, Y. Offret, *Persistent random walks. I. Recurrence versus transience* | 31 (2018) 232–243 | 10.1007/s10959-016-0714-4 | Medium. JTP's own persistent-walk papers. |
| 4 | P. Cénac, A. Le Ny, B. de Loynes, Y. Offret, *Persistent random walks. II. Functional scaling limits* | 32 (2019) 633–658 | 10.1007/s10959-018-0852-y | Medium. |
| 5 | M. Podder, A. Roy, *Elephant random walks with multiple extractions and general reinforcement functions* | 39 (2026) art. 17 | 10.1007/s10959-025-01471-4 | Low to medium. The most recent JTP ERW paper (65 refs). |
| 6 | A. Gut, U. Stadtmüller, *Bernoulli elephant random walks* | 39 (2026) art. 60 | 10.1007/s10959-026-01517-1 | Medium. Steps in {0,1}, a biased first step and the number of zeros. This is the count A_N that D uses. It also corrects earlier ERW-with-delays results. |
| 7 | E. Althaus, L. Hartung, R. Steiner, *A random walk approach to broadcasting on random recursive trees* | 39 (2026) art. 65 | 10.1007/s10959-026-01519-z | High. See Section 3. Its colour-difference process is exactly D's walk. |
| 8 | S. Bhattacharya, S. Volkov, *Two-dimensional Rademacher walk* | 39 (2026) art. 40 | 10.1007/s10959-026-01497-2 | Low. Cites the Engländer–Volkov coin-turning book. |
| 9 | D. Cheliotis, D. Kouloumpou, *Functional limit theorems for the Pólya urn* | 35 (2022) 2038–2051 | 10.1007/s10959-021-01123-3 | Low. Urn context. |
| 10 | S. Janson, *Moments of balanced Pólya urns* | 38 (2025) art. 75 | 10.1007/s10959-025-01447-4 | Low. Urn context. |
| 11 | W. M. Ruszel, D. Thacker, *Positive reinforced generalized time-dependent Pólya urns via stochastic approximation* | 37 (2024) 2859–2885 | 10.1007/s10959-024-01366-w | Low. |
| 12 | Y. Dahiya, N. Sahasrabudhe, *Urns with multiple drawings and graph-based interaction* | 37 (2024) 3283–3316 | 10.1007/s10959-024-01365-x | Low. |
| 13 | J. Shi, Z. Yu, Y. Miao, *The law of the iterated logarithm for the nonlinear unbalanced urn model* | 39 (2026) art. 39 | 10.1007/s10959-026-01498-1 | Low. |
| 14 | B. Davis, J. Peterson, *Excited random walks with non-nearest neighbor steps* | 30 (2017) 1255–1284 | 10.1007/s10959-016-0697-1 | Low. Self-interacting walk. |
| 15 | J. Leppänen, *A local limit theorem for a random walk in an intermittent dynamical environment* | 39 (2026) art. 20 | 10.1007/s10959-025-01478-x | Low. A JTP local limit theorem for a dependent walk. |
| 16 | Y. Hafouta, Y. Kifer, *A nonconventional local limit theorem* | 29 (2016) 1524–1553 | 10.1007/s10959-015-0625-9 | Low. |

None of the JTP papers I found gives an exact or local law of the ERW endpoint at finite n, or compares the
middle with the ends. The closest JTP papers are 1 (the end versus middle shape for the persistent walk with
p_n = a/n) and 7 (the same model as D, studied as root-bit reconstruction for small q).

**Not found.** I found no Kiss–Laulin paper. The likely intended paper is J. Kiss and B. Vető, *Moments of the
superdiffusive elephant random walk with general step distribution*, Electron. Commun. Probab. 27 (2022),
paper 44, 1–12, doi:10.1214/22-ECP485. The paper on how often a critical ERW returns to the origin is by
Z. Fang (ECP 29, 2024), not by Bertoin. GLRS 2025 is EJP 30 (2025), doi:10.1214/25-EJP1362, which D already cites.

## 2. How the JTP papers are written

- **Length.** The two Cénac et al. papers run 12 and 26 pages and Engländer–Volkov runs 22. Gut–Stadtmüller
  has 13 references and reads like a short note. Podder–Roy is long (65 references). Paper D is 49 pages,
  which would be long for a JTP paper on this topic. Moving material to an appendix or a supplement would help.
- **Introductions.** Engländer–Volkov defines the model in its first paragraph and has no stand-alone main
  theorem. Its results are Theorems 1 to 4, one section per regime (supercritical, critical a/n, subcritical
  a/n^γ, and LLN criteria), and it ends with a heuristics-and-conjecture section. Althaus–Hartung–Steiner
  gives Definitions 1 to 4 in the introduction, then a "Related results" paragraph and an outline, and states
  its main theorems (Theorems 5 and 6) at the start of Section 2. Both say what is new quickly and briefly.
  Neither has a long heuristic part before the theorems. D's heuristic paragraphs ("Why the elephant needs
  twice as many reversals") come before its precise statements. They are good, but D should put the Main
  Theorem first or keep the heuristics short.
- **Main results up front.** Paper D's "Main Theorem" block is in line with current JTP practice. Its Results
  subsection also lists about 20 more propositions and theorems in running prose. JTP readers would expect
  two or three numbered headline theorems, with the rest in the body.
- **Computer verification.** None of the JTP memory-walk papers I found uses certified computation. They are
  purely analytic, with at most a figure. D relies on interval or ball arithmetic for 10 ≤ N ≤ 2000 and on a
  floating-point check with a bounded error for N < 1688. A JTP referee will accept this if the proved and
  certified parts are kept clearly apart, and the paper's Section 5 and its data statement do this. It would
  help to state in the introduction exactly which statements depend on computation, as D's Main Theorem (b)
  already partly does.
- **References.** These range from 8 to 65 references. Gut–Stadtmüller and Engländer–Volkov rely on short
  lists of core papers. Podder–Roy and Althaus et al. survey widely.
- **Time from submission to acceptance:** Podder–Roy about 4 months, Gut–Stadtmüller about 8.5 months,
  Althaus et al. about 8 months, Bhattacharya–Volkov about 9 months.
- **Submission rules.** I could not read the guidelines (login wall). D already has keywords, MSC 2020 codes,
  and statements on competing interests, funding and data. These are the standard Springer items.

## 3. Work Paper D does not cite but a JTP referee would expect

Checked against `sec_intro.tex` (including Section 1.4, Prior work) and the bibliography in
`problem131_memory.tex`. No .tex file in paperD mentions broadcasting, coin turning, Engländer, Gut or Cénac.

### Must cite

1. **Broadcasting on random recursive trees. This is the same model as D under another name.** On the uniform
   random recursive tree, each new vertex copies its parent's bit and flips it with probability q. That is
   D's walk with ε = q: the root bit is X_1 and the number of red vertices is A_N. The majority-vote error
   R_maj(N,q) = P(Δ(N)<0) + ½P(Δ(N)=0) is built from the same law P_N. So D's "middle" C_N is exactly the
   tie term P(Δ(N)=0).
   - L. Addario-Berry, L. Devroye, G. Lugosi, V. Velona, *Broadcasting on random recursive trees*, Ann. Appl.
     Probab. 32 (2022), 497–528. doi:10.1214/21-AAP1686. They identify the q for which the root bit can be
     recovered (majority is informative exactly when q < 1/4) and prove that the error is O(q).
   - E. Althaus, L. Hartung, R. Steiner, *A random walk approach to broadcasting on random recursive trees*,
     J. Theoret. Probab. 39 (2026), art. 65. doi:10.1007/s10959-026-01519-z (arXiv:2405.04385). In JTP itself,
     they treat the colour difference explicitly as an ERW. They prove that R_maj(q) = ½ for q ≥ 1/4 (in the
     uniform case) and that R_maj(q) ≤ c√q for small q. Their limit is for fixed q as N → ∞, which is the
     contrast D's prior-work section should make.
   - C. Desmarais, C. Holmgren, S. Wagner, *Broadcasting-induced colorings of preferential attachment trees*,
     Random Structures Algorithms 63 (2023), 364–405. doi:10.1002/rsa.21142. They prove rescaled limit laws for
     the number of vertices of each colour through Pólya urns, and they study the root cluster with analytic
     combinatorics. Both are close to D's cluster picture and to its view of the center as a large deviation
     of the root cluster.
     Companion: C. Desmarais, C. Holmgren, S. Wagner, *The root cluster after percolation on preferential
     attachment trees*, Proc. EUROCOMB 2023, 343–348. doi:10.5817/CZ.MUNI.EUROCOMB23-047.
   - T. Kardas, V. Shneer, V. Wachtel, *Broadcasting on random trees: martingale methods and error bounds*,
     preprint 2026, arXiv:2606.22960. It gives error bounds linear in q for the majority rule over a broad class of trees.

   Suggested addition to Section 1.4: one paragraph noting that the walk is the colour count of
   broadcasting on a uniform random recursive tree [ADLV22, AHS26, DHW23], that this literature studies the
   majority error for fixed q, and that D's center probability is the tie probability at q = x/N → 0. The
   sentence "We did not find an asymptotic formula ... in the elephant-walk, percolation or Luria–Delbrück
   literature" should then also name the broadcasting literature.

2. **Coin-turning walks**, the JTP model closest to D's persistent-walk comparison. The time-inhomogeneous
   persistent walk with p_n = a/n has limit Beta(a,a). The U-shape for a<1 against the hump for a>1 is the
   scaling-limit version of D's question of ends against middle. Cite as the persistent-walk analogue in the
   introduction's paragraph on the persistent walk, and perhaps in the conclusion.
   - J. Engländer, S. Volkov, *Turning a coin over instead of tossing it*, J. Theoret. Probab. 31 (2018),
     1097–1118. doi:10.1007/s10959-016-0725-1.
   - J. Engländer, S. Volkov, Z. Wang, *The coin-turning walk and its scaling limit*, Electron. J. Probab. 25
     (2020), paper no. 3, 1–38. doi:10.1214/19-EJP406.
   - J. Engländer, S. Volkov, *Coin-Turning, Random Walks and Inhomogeneous Markov Chains*, World Scientific,
     Singapore, 2024. doi:10.1142/13837. (Bhattacharya–Volkov list it as 2025.)

3. **The GLR fixed-point paper**, a companion to GLRS, which D cites. GLRS's unimodality and log-concavity
   questions come out of it.
   - H. Guérin, L. Laulin, K. Raschel, *A fixed-point equation approach for the superdiffusive elephant random
     walk*, Ann. Inst. Henri Poincaré Probab. Stat. 62 (2026), 973–1005. doi:10.1214/24-AIHP1534 (arXiv:2308.14630).

4. **Exact finite-n computations for the ERW.** A referee will ask how D's counting chain and exact law relate
   to these.
   - B. Bercu, M.-L. Chabanol, J.-J. Ruch, *Hypergeometric identities arising from the elephant random walk*,
     J. Math. Anal. Appl. 480 (2019), 123360. doi:10.1016/j.jmaa.2019.07.050.
   - J. Kiss, B. Vető, *Moments of the superdiffusive elephant random walk with general step distribution*,
     Electron. Commun. Probab. 27 (2022), paper 44, 1–12. doi:10.1214/22-ECP485.
   - M. A. A. da Silva, J. C. Cressoni, G. M. Schütz, G. M. Viswanathan, S. Trimper, *Non-Gaussian propagator
     for elephant random walks*, Phys. Rev. E 88 (2013), 022115. doi:10.1103/PhysRevE.88.022115.

### Should cite (JTP context and the 0/1 count)

5. A. Gut, U. Stadtmüller, *Bernoulli elephant random walks*, J. Theoret. Probab. 39 (2026), art. 60.
   doi:10.1007/s10959-026-01517-1. This is the ERW with {0,1} steps and a biased first step, the JTP
   counterpart of D's A_N and of the Miyazaki–Takei laziest walk that D already cites. Its survey: A. Gut,
   U. Stadtmüller, *Elephant random walks; a review*, Ann. Univ. Sci. Budapest. Sect. Comput. 54 (2023),
   171–198 (DOI not checked).
6. P. Cénac, A. Le Ny, B. de Loynes, Y. Offret, *Persistent random walks. I*, J. Theoret. Probab. 31 (2018),
   232–243, doi:10.1007/s10959-016-0714-4; and *II. Functional scaling limits*, J. Theoret. Probab. 32 (2019),
   633–658, doi:10.1007/s10959-018-0852-y. These are JTP's own references for persistent walks.

### Optional (recent, near D, with lower risk if left out)

7. H. Trinas, G. Valle, arXiv:2609.14753 (2026). D already cites this. Note that it, like D, rests on an exact
   recurrence for the mass function, and that it disproves the GLRS eventual log-concavity conjecture. D could
   say how its counting chain compares with their recurrence.
8. Z. Fang, *How often does a critical elephant random walk return to origin*, Electron. Commun. Probab. 29
   (2024), 1–12. doi:10.1214/24-ECP636. This follows Bertoin's zero counting.
9. X. Fan, Y. Qi, *A generalized elephant random walk with time-dependent memory*, arXiv:2610.16065 (October
   2026). Here the memory parameter p_n varies with time, but it does not vary with the horizon N as D's does.
10. R. Roy, M. Takei, H. Tanemura, *The elephant random walk in the triangular array setting*, J. Appl. Probab.
    62 (2025), 997–1009 (arXiv:2403.02881; DOI not checked). Here the memory size varies with n, not the reversal probability.
11. P. Vishwakarma, *Moments approach for the elephant random walk*, arXiv:2609.11035 (2026). J. E. González
    Rangel, *Asymptotics for the Laplace transform of the elephant random walk via Schwarz–Christoffel
    mappings*, arXiv:2607.15125 (2026). Both work with exact recurrences or generating functions at finite n.
12. M. Podder, A. Roy, J. Theoret. Probab. 39 (2026), art. 17, doi:10.1007/s10959-025-01471-4. It shows the
    journal publishes ERW work, but it is not close to D in content.

## 4. Key points for the revision

- The most serious gap is the **broadcasting literature** (ADLV 2022 AAP, Althaus–Hartung–Steiner 2026 JTP,
  DHW 2023 RSA). It studies exactly D's law, P_N on the uniform random recursive tree with flip probability q,
  and the JTP paper names the ERW link explicitly. A JTP referee who knows that paper would expect it to be
  cited and the regimes compared: fixed q with N → ∞ there, against q = x/N with x ≍ log N in D.
- **Coin turning** (Engländer–Volkov, JTP 2018) is JTP's own persistent-walk model with vanishing turning
  probability. Its Beta(a,a) limit, U-shaped against humped, is the scaling-limit analogue of D's crossing.
- Cite **GLR 2026 (AIHP)** together with GLRS, and cite the finite-n exact results (Bercu–Chabanol–Ruch,
  Kiss–Vető, da Silva et al.).
- **Shape for JTP:** D is long at 49 pages. Make the opening tighter, with two or three numbered headline
  theorems and the heuristics after them or shortened, and say clearly which statements depend on
  certified computation. None of the JTP memory-walk papers found uses computer certification. That is not
  disqualifying, but D needs to state the division between proof and computation clearly.

## Sources

- Crossref API, journal 0894-9840 (all records from 2015) and works lookups.
- https://arxiv.org/abs/1606.03281 (Engländer–Volkov, read in full)
- https://arxiv.org/abs/2405.04385 (Althaus–Hartung–Steiner, read in full)
- https://arxiv.org/abs/2606.22960, https://arxiv.org/abs/2609.14753, https://arxiv.org/abs/2609.11035,
  https://arxiv.org/abs/2607.15125, https://arxiv.org/abs/2610.16065, https://arxiv.org/abs/2604.07227,
  https://arxiv.org/abs/2507.14626, https://arxiv.org/abs/2403.02881, https://arxiv.org/abs/2308.14630,
  https://arxiv.org/abs/2110.15050, https://arxiv.org/abs/2112.00066, https://arxiv.org/abs/1509.03882,
  https://arxiv.org/abs/1612.00238
- https://projecteuclid.org/journals/annals-of-applied-probability/volume-32/issue-1/Broadcasting-on-random-recursive-trees/10.1214/21-AAP1686.full
- https://projecteuclid.org/journals/electronic-journal-of-probability/volume-25/issue-none/The-coin-turning-walk-and-its-scaling-limit/10.1214/19-EJP406.pdf
