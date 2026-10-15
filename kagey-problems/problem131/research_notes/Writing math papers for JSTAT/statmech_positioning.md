# Statistical-mechanics positioning of the persistent random walk / 1D Ising magnetization crossing paper (target: JSTAT)

Notation used below. Paper: p = probability of repeating the previous step; u = (1-p)/p; z_N = N(1-p_N). Ising dictionary (free BC, zero field, coupling K = beta*J): P(spin flip between neighbours) = e^{-K}/(2 cosh K) = 1-p, so 2p-1 = tanh K, and Antal-Droz-Racz's t = 1 - tanh K = 2(1-p). The ADR scaling variable is zeta = N t / 2 = N(1-p). **So the paper's z_N is exactly the standard finite-size scaling variable of the 1D Ising chain** (half the mean number of domain walls, N/(2 xi) with xi = -1/log(2p-1) ~ 1/(2(1-p))). These identifications are my own algebra from the definitions in the ADR paper, not quotes.

## Q1. Exact magnetization distribution of the finite 1D Ising chain; is the end-vs-centre crossing known?

### Takeaway
The exact finite-size scaling form of the magnetization distribution for free and periodic BC is known (Bruce 1981 for blocks, which equal free BC; Antal-Droz-Racz 2004 for periodic, antiperiodic, free and block BC). It has delta peaks at m = +/-1 plus a Bessel I0/I1 continuum. **The "fully magnetized = zero magnetization" crossing has also been posed explicitly**, by Stepanyan, Tzortzakakis, Petrosyan and Allahverdyan in **JSTAT 2024**, for periodic BC and with only a heuristic log N scaling. The submission has to cite both and present itself as the sharp, rigorous and uniform version of what they did.

### Cited Findings
- **Antal, Droz, Racz, "Probability distribution of magnetization in the one-dimensional Ising model: effects of boundary conditions", J. Phys. A: Math. Gen. 37, 1465-1478 (2004), DOI 10.1088/0305-4470/37/5/001, arXiv:cond-mat/0308442** (DOI and metadata verified via Crossref and the arXiv abstract page). — [arXiv](https://arxiv.org/abs/cond-mat/0308442); [DOI](https://doi.org/10.1088/0305-4470/37/5/001)
  - Scaling limit: T -> 0 and N -> infinity with N[1 - tanh(J/k_BT)] finite. Exact results for periodic, antiperiodic, free and block BC. — [arXiv](https://arxiv.org/abs/cond-mat/0308442)
  - "2 zeta = N t = N/xi, i.e. 2 zeta is the average number of domains (or domain walls) in the system." — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
  - Periodic BC, Eq. (37): P(m) = [delta(m+1)+delta(m-1)]/(2 cosh zeta) + zeta I1(zeta sqrt(1-m^2)) / (2 sqrt(1-m^2) cosh zeta). — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
  - Free BC, Eq. (47): P(m) = (e^{-zeta}/2)[delta(m+1)+delta(m-1)] + (zeta e^{-zeta}/2) I1(zeta sqrt(1-m^2))/sqrt(1-m^2) + (zeta e^{-zeta}/2) I0(zeta sqrt(1-m^2)). Free and periodic are related by Eq. (46): P^f = e^{-zeta}[cosh zeta P^p + sinh zeta P^a]. — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
  - "the coefficient of the singular part is larger for the periodic case, i.e., a periodic system is more likely to be in the completely ordered steady state." — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
  - For large zeta a Gaussian approximation holds, P(m) ~ (2 pi zeta)^{-1/2} exp(-m^2 zeta/2), obtained from I0(x) ~ I1(x) ~ e^x/sqrt(2 pi x). For small zeta the distribution is the delta peaks plus a near-constant background. ADR do **not** define or locate an end-vs-centre crossing. — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
  - The block-magnetization distribution of a free chain equals the free-BC distribution for every block length (proved by integrating out the outer spins). — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
  - They motivate the problem through Bruce's programme of using order-parameter distribution scaling functions as "hallmarks of universality classes" and through finite-size scaling (Fisher, Barber, Cardy, Binder 1981). — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
- **A. D. Bruce, "Probability density functions for collective coordinates in Ising-like systems", J. Phys. C: Solid State Phys. 14, 3667-3688 (1981), DOI 10.1088/0022-3719/14/25/012** (verified via Crossref). The block distribution depends on L/xi; in 1D it is "controlled by the statistics of kinks", and the critical limit has an "extreme order-disorder character". ADR state that their free-BC Eq. (47) reproduces Bruce's Eq. (3.20). — [DOI](https://doi.org/10.1088/0022-3719/14/25/012); [ADR](https://arxiv.org/pdf/cond-mat/0308442)
- **Stepanyan, Tzortzakakis, Petrosyan, Allahverdyan, "Thermal transitions in a one-dimensional, finite-size Ising model", J. Stat. Mech. (2024) 033202, DOI 10.1088/1742-5468/ad2679, arXiv:2307.15479** (verified via Crossref). This is the most dangerous overlap.
  - Periodic BC. Exact P_m and domain-wall distributions; "several temperatures" analogous to first-order transition points. — [arXiv](https://arxiv.org/abs/2307.15479)
  - T_tr(1) is defined by P(m = +/-N) = P(|m| = N-2), which gives beta_tr(1) = ln N/(4J). — [arXiv HTML](https://arxiv.org/html/2307.15479v3) (summary from a WebFetch extraction)
  - **T_tr(2) is defined by "P_{m=+/-N} = P_{m=0}", i.e. ferromagnetic and paramagnetic states equally probable, with beta_tr(2) ~ [2 ln N - 1]/(5J).** This is the paper's crossing (periodic case) at a heuristic level. — [arXiv HTML](https://arxiv.org/html/2307.15479v3) (WebFetch extraction; the exact equation should be re-read in the PDF before quoting)
  - A dynamical temperature defined by equal residence times gives beta_tr(d) ~ (3/(17J)) ln N, a fit. — [arXiv HTML](https://arxiv.org/html/2307.15479v3)
  - For the magnetization distribution they cite Bruce 1981, ADR 2004 and Xu & del Campo, PRL 122, 160602 (2019) (DOI 10.1103/PhysRevLett.122.160602, verified). For domain walls they cite Yilmaz & Zimmermann, "Exact cluster size distribution in the one-dimensional Ising model", PRE 71, 026127 (2005) (DOI 10.1103/PhysRevE.71.026127, verified). — [arXiv HTML](https://arxiv.org/html/2307.15479v3); [Crossref-verified DOIs](https://doi.org/10.1103/PhysRevLett.122.160602), [PRE](https://doi.org/10.1103/PhysRevE.71.026127)
- Eisele & Ellis, "Symmetry breaking and random waves for magnetic systems on a circle". Title and authors verified via Crossref, DOI 10.1007/BF00542534. My recollection is Z. Wahrscheinlichkeitstheorie verw. Gebiete 63 (1983) 297-348, but **journal, volume, pages and year are not verified**. This is a probability treatment of magnetization limit laws; I did not check whether it treats 1D finite-size distributions. — [DOI](https://doi.org/10.1007/BF00542534)
- A fixed-M ensemble paper gives exact partition functions of the 1D Ising chain at fixed magnetization for different BC by domain counting (arXiv:2207.01134; authors and journal **not verified**). — [arXiv](https://arxiv.org/pdf/2207.01134)

### Inferences
- **The paper's crossing equation can be recovered at leading order from the ADR free-BC scaling function** (my own calculation, worth stating in the paper). Each end peak has weight e^{-zeta}/2. The middle bin has width Delta m = 2/N, so its probability is about (zeta e^{-zeta}/N)(I0(zeta)+I1(zeta)). Using I0+I1 ~ 2e^zeta (2 pi zeta)^{-1/2}(1 - 1/(8 zeta)), the equality becomes zeta + (1/2) log zeta = log N + (1/2) log(pi/8) + 1/(8 zeta) + ..., which is the paper's equation without R_N, including the 1/(8z) term. A JSTAT referee who knows ADR will notice this. The paper should therefore say plainly that the heuristic follows from the known scaling function. Its contribution is:
  - (a) the crossing sits at zeta ~ log N -> infinity, **outside the fixed-zeta scaling window** ADR work in, so the scaling function alone does not justify it;
  - (b) the uniform, explicit, non-asymptotic Bessel bounds (relative error <= N u^2/2 + u), together with existence and uniqueness of p_N and control of R_N;
  - (c) the exact finite-N laws with the free-vs-periodic comparison.
- **Free vs periodic.** The periodic end weight 1/(2 cosh zeta) ~ e^{-zeta} is about twice the free one, and the periodic continuum at m=0 is (zeta/(2 cosh zeta)) I1(zeta). The same heuristic then gives zeta + (1/2) log zeta ~ log N + (1/2) log(pi/2) for periodic BC (my calculation; parity and lattice-spacing details need checking against the paper's own periodic result). With zeta ~ N e^{-2K}, this means beta J ~ (1/2) ln N - (1/2) ln ln N + O(1). Stepanyan et al report beta_tr(2) ~ (2 ln N - 1)/(5J), a 2/5 slope. That may be a fit, a different J convention, or an error. **The submission can position itself as giving the exact asymptotics (and correcting the coefficient, if confirmed) of the JSTAT 2024 "T_tr(2)" transition.** Verify their Hamiltonian normalization before claiming any discrepancy.
- Physical reading in Ising language: the crossing is the temperature at which the fully ordered (single-domain) state stops dominating the zero-magnetization sector of a finite chain. Equivalently, the chain holds about 2 zeta_N ~ 2 log N domain walls, or N ~ 2 xi log N. This is the "finite-size pseudo-transition temperature T_N ~ 2J/ln N" language used for the 1D Ising chain.

### Gaps
- Kac's own work on Ising magnetization distributions: no specific paper found in this search budget. The Kac 1974 item below is the telegraph paper, not Ising.
- "Hidaka": no relevant 1D Ising magnetization-distribution paper by this name found. Treat as unverified or likely nonexistent.
- I did not read the Stepanyan et al PDF directly; the T_tr(2) formula and quotation come from a WebFetch extraction of the arXiv HTML. Re-read it before citing.
- Not checked: whether Xu & del Campo (2019) give a finite-N exact formula usable as a citation for the periodic law.

## Q2. Persistent / correlated random walk, telegraph process and run-and-tumble exact distributions

### Takeaway
The canonical lineage is: Goldstein 1951 and Kac 1974 (telegraph process; continuum limit of the persistent walk); Renshaw & Henderson 1981 (exact lattice correlated random walk law); the Weiss and Masoliver-Lindenberg physics literature on persistent walks; and Malakar et al JSTAT 2018 for run-and-tumble particles (RTPs). In the active-matter version, the propagator is ballistic delta peaks at +/-vt with weight e^{-gamma t} plus a Bessel continuum that becomes Gaussian at late times. This is the continuum counterpart of the ADR Ising law.

### Cited Findings
- **S. Goldstein, "On diffusion by discontinuous movements, and on the telegraph equation", Q. J. Mech. Appl. Math. 4, 129-156 (1951), DOI 10.1093/qjmam/4.2.129** (verified via Crossref). — [DOI](https://doi.org/10.1093/qjmam/4.2.129)
- **M. Kac, "A stochastic model related to the telegrapher's equation", Rocky Mountain J. Math. 4 (1974), DOI 10.1216/RMJ-1974-4-3-497** (verified via Crossref; pages 497-509 from the DOI suffix plus memory, end page unverified). — [DOI](https://doi.org/10.1216/RMJ-1974-4-3-497)
- **E. Renshaw & R. Henderson, "The correlated random walk", J. Appl. Probab. 18, 403-414 (1981), DOI 10.2307/3213286** (verified). They give an expression for P(X_n = k) on Z and its limit as n -> infinity with the persistence parameter -> 1. — [DOI](https://doi.org/10.2307/3213286); [snippet via arXiv:quant-ph/0310191](https://arxiv.org/html/quant-ph/0310191)
- Chen & Renshaw, correlated walks in higher dimensions / general walk, J. Appl. Probab. 31, 869-884 (1994) (from a search snippet; **not independently verified**). — [arXiv:quant-ph/0310191](https://arxiv.org/html/quant-ph/0310191)
- **G. H. Weiss, "Some applications of persistent random walks and the telegrapher's equation", Physica A 311, 381-410 (2002), DOI 10.1016/S0378-4371(02)00805-1** (verified). This is the standard physics review of persistent walks. — [DOI](https://doi.org/10.1016/S0378-4371(02)00805-1)
- **Masoliver, Lindenberg, Weiss, "A continuous-time generalization of the persistent random walk", Physica A 157, 891-898 (1989), DOI 10.1016/0378-4371(89)90071-X** (verified). — [DOI](https://doi.org/10.1016/0378-4371(89)90071-X)
- **Masoliver & Lindenberg, "Continuous time persistent random walk: a review and some generalizations", Eur. Phys. J. B 90, 107 (2017), DOI 10.1140/epjb/e2017-80123-7** (verified). Recent review, good for a single "see review" citation. — [DOI](https://doi.org/10.1140/epjb/e2017-80123-7)
- Masoliver, Porra, Weiss, "Some two and three-dimensional persistent random walks", Physica A 193, 469-482 (1993), DOI 10.1016/0378-4371(93)90488-P (verified; optional). — [DOI](https://doi.org/10.1016/0378-4371(93)90488-P)
- Herrmann & Vallois, "From persistent random walk to the telegraph noise", Stoch. Dyn. 10, 161-196 (2010), DOI 10.1142/S0219493710002905 (verified). A probability-side scaling-limit reference. — [DOI](https://doi.org/10.1142/S0219493710002905)
- **Malakar, Jemseena, Kundu, Vijay Kumar, Sabhapandit, Majumdar, Redner, Dhar, "Steady state, relaxation and first-passage properties of a run-and-tumble particle in one-dimension", J. Stat. Mech. (2018) 043215, DOI 10.1088/1742-5468/aab84f, arXiv:1711.08474** (verified). The exact distribution on the line, with and without diffusion, approaches a Gaussian at long times but "exhibits unexpected multi-modal forms" at intermediate times. In a finite interval the steady state has peaks at the boundaries. — [arXiv](https://arxiv.org/abs/1711.08474); [DOI](https://doi.org/10.1088/1742-5468/aab84f)
- **Bechinger, Di Leonardo, Lowen, Reichhardt, Volpe, Volpe, "Active particles in complex and crowded environments", Rev. Mod. Phys. 88, 045006 (2016), DOI 10.1103/RevModPhys.88.045006** (verified). — [DOI](https://doi.org/10.1103/RevModPhys.88.045006)
- Mori, Le Doussal, Majumdar, Schehr, "Condensation transition in the late-time position of a run-and-tumble particle", PRE 103, 062134 (2021), DOI 10.1103/PhysRevE.103.062134 (verified bibliographically; **content not read**). By its title it concerns a large-deviation "condensation" where one run dominates, which is related to ballistic end-peak dominance and worth checking. — [DOI](https://doi.org/10.1103/PhysRevE.103.062134)
- Pradhan, Roy, Ray, "Diffusive-to-Ballistic transition in a Persistent Random Walk", arXiv:2605.20116 (May 2026, preprint). Time-dependent reversal probability ~ power law with a transition at alpha = 1, characterized through a Binder cumulant and finite-time scaling. Not the same question, but recent and in JSTAT's audience. — [arXiv](https://arxiv.org/abs/2605.20116)
- Textbooks (bibliographic data partly from memory, **not verified here**): G. H. Weiss, *Aspects and Applications of the Random Walk* (North-Holland, 1994); B. D. Hughes, *Random Walks and Random Environments, Vol. 1: Random Walks* (Oxford, 1995). Crossref shows an OUP 1995 chapter DOI 10.1093/oso/9780198537885.003.0002 for Hughes Vol. 1. — [Crossref/OUP](https://doi.org/10.1093/oso/9780198537885.003.0002)

### Inferences
- The Bessel form of the lattice law is the discrete analogue of the telegraph / RTP propagator, whose continuum part involves I0 and I1 of gamma sqrt(t^2 - x^2/v^2) (standard Kac/Goldstein result; not re-derived from a fetched source here). The ADR Ising formula (zeta sqrt(1-m^2) arguments) is literally the telegraph propagator with gamma t <-> zeta and x/(vt) <-> m. The paper can unify the Ising, RTP and Galton-board pictures in one paragraph.
- The paper's p -> 1 regime with N(1-p) of order log N corresponds in RTP language to the time window where the number of tumbles gamma t is about log(vt/ell) for lattice spacing ell.

### Gaps
- I did not fetch Renshaw-Henderson or Weiss's book to confirm the exact form of their lattice formula (binomial-sum vs Bessel). The search snippet does not confirm a Bessel form.
- Stadje's persistent-walk papers were not searched within budget.

## Q3. Is "end peak = centre" at N(1-p) ~ log N known in active matter / RTP literature?

### Takeaway
I found no RTP or active-matter paper that defines the time at which the ballistic delta peaks at x = +/-vt equal the central density, or that derives a gamma t ~ log t law. In Ising language, however, Stepanyan et al JSTAT 2024 define exactly this crossing for periodic chains, heuristically.

### Cited Findings
- Malakar et al 2018 discuss multimodal intermediate-time forms and Gaussian late-time forms but (per the abstract) do not single out an end-equals-centre time. — [arXiv](https://arxiv.org/abs/1711.08474)
- Stepanyan et al 2024: "P_{m=+/-N} = P_{m=0}" crossing, periodic BC, beta ~ (2 ln N - 1)/(5J). — [arXiv HTML](https://arxiv.org/html/2307.15479v3)
- A search for an exact discrete-time lattice RTP propagator with an explicit ballistic-diffusive crossover returned nothing matching; the crossover is described qualitatively ("ballistic at short times and diffusive at long times"). — [search results incl. Frontiers review](https://www.frontiersin.org/journals/physics/articles/10.3389/fphy.2019.00120/xml)

### Inferences
- The novelty for JSTAT is not the existence of the crossing but its **sharp location** (log N plus the (1/2) log z correction, the constant (1/2) log(pi/8) and 1/(8z) with a controlled remainder), its **boundary-condition dependence** (free vs periodic constants), and **uniform error bounds** valid where the fixed-zeta scaling theory fails.
- Suggested framing: "a finite-size order-disorder crossover beyond the scaling window", or "the ballistic-diffusive crossover of a lattice run-and-tumble particle, located exactly".

### Gaps
- Not checked: Mori et al 2021 condensation paper and the extremal-statistics RTP paper (arXiv:2208.08792) in full; either might contain an analogous peak-weight comparison.

## Q4. Physical observables and finite-size-scaling language; venue map

### Takeaway
The crossing is controlled by the number of domain walls (tumbles, switches, kinks), whose mean is (N-1)(1-p) ~ z_N. The scaling variable is N/xi (ADR's 2 zeta). JSTAT readers will expect: finite-size scaling variable, correlation length, a pseudo-critical temperature T_N ~ 1/ln N, boundary-condition dependence of scaling functions, and the delta-plus-continuum ("order-disorder") structure of the order-parameter distribution.

### Cited Findings
- 2 zeta = N t = N/xi is the mean number of domains or domain walls. Correlations decay as v^n = e^{-n/xi} with v = tanh K. ADR argue this exponential-decay definition of xi (not the second-moment one) is the right one for finite-size scaling. — [arXiv PDF](https://arxiv.org/pdf/cond-mat/0308442)
- Bruce: the 1D block distribution is "controlled by the statistics of kinks" with "extreme order-disorder character". — [DOI](https://doi.org/10.1088/0022-3719/14/25/012)
- Stepanyan et al use the language of "temperatures resembling critical temperatures of first-order phase transitions" and residence times, with application to biopolymer structural transitions. — [arXiv](https://arxiv.org/abs/2307.15479)
- Venues (all verified via Crossref):
  - JSTAT: Malakar et al 2018; Stepanyan et al 2024.
  - J. Phys. A: Antal-Droz-Racz 2004.
  - J. Phys. C: Bruce 1981.
  - PRE: Yilmaz-Zimmermann 2005; Mori et al 2021; Sadjadi-Miri 2008 (persistent walk with random transmittances, PRE 78, 061114).
  - PRL: Xu-del Campo 2019.
  - RMP: Bechinger et al 2016.
  - Physica A: Weiss 2002; Masoliver-Lindenberg-Weiss 1989.
  - EPJ B: Masoliver-Lindenberg 2017.
  - J. Appl. Probab.: Renshaw-Henderson 1981.
  - QJMAM: Goldstein 1951.
  - Rocky Mountain J. Math.: Kac 1974.
  — [Crossref records via DOIs above](https://api.crossref.org/works/10.1088/1742-5468/ad2679)

### Inferences
- Dictionary to put in the paper:
  - p <-> e^K/(2 cosh K)
  - 2p-1 = tanh K
  - xi = -1/log(2p-1)
  - z_N = N(1-p) = ADR's zeta, about N/(2 xi), i.e. half the mean number of domain walls
  - crossing at N/xi ~ 2 log N, i.e. k_B T_N ~ 2J/ln N for free BC at leading order
  - right steps <-> up spins, bin <-> M = 2(bin) - N
  - tumbles <-> domain walls
  - Laguerre law for fixed bins <-> fixed small number of domain walls, ADR's small-zeta, fixed-g expansion
- Recommended positioning sentence: "The finite-size scaling function of the magnetization distribution is known (Bruce 1981; Antal, Droz and Racz 2004), and the equal-probability temperature of ordered and disordered states was recently discussed for periodic chains (Stepanyan et al 2024). Here we locate this crossing exactly. It lies at zeta = N/(2 xi) ~ log N, outside the fixed-zeta scaling regime, and we give uniform non-asymptotic Bessel bounds that justify the scaling-function heuristic there for both free and periodic boundaries."

### Gaps
- No textbook (Baxter, Weiss, Hughes) was checked for the finite-N magnetization law.
- No JSTAT-specific editorial guidance on rigorous-math contributions was gathered (outside this scope).
