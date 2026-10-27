# 05. Literature check for the merged paper (F plus G)

Date of check: 2026-10-26. Scope: the sources listed in the F plan (v2), plus a search for 2023-2026 work.

## Reading status key

- FULL = I downloaded the arXiv PDF and read the parts named (introduction, theorem statements, sections listed). Proofs were not read.
- ABSTRACT = known only from the abstract or journal record (Crossref, search snippets) and from how other papers cite it.
- DOIs, volumes and pages were taken from Crossref records.

## What the two papers already cite

- Paper F cites: Akimoto 2023 (PRE 108, 054113), Godreche-Luck 2001, Lamperti 1958, Zaburdaev-Denisov-Klafter 2015, Wang-Schulz-Deng-Barkai 2018, Wang-Vezzani-Burioni-Barkai 2019, Vezzani-Barkai-Burioni 2019 and 2020, Wang-Hoell-Barkai 2020, Rebenshtok et al. 2014 (two papers), Berger (EJP 2019, PTRF 2019), Caravenna-Doney 2019, Doney (1989, 1991, 2023), Denisov-Dieker-Shneer 2008, Rozovskii 1993 and 1997, Takacs 1957 and 1959, Kesten 1962, Schulz-Barkai 2015, Berger-Birkner-Yuan 2024.
- Paper F does not cite: Starreveld-Bekker-Mandjes, Mitov-Yanev, Doney 1997, Horii-Lefevere-Nemoto, Lefevere-Mariani-Zambotti, the three teletraffic on/off papers, Baldassarri et al., Akimoto-Sera-Yamato-Yano 2020, Barbe-McCormick.
- Paper G cites: Starreveld-Bekker-Mandjes, Mitov-Yanev, Godreche-Luck, Lamperti, Margolin-Barkai 2006, Wang-Schulz-Deng-Barkai 2018, Zaburdaev-Denisov-Klafter, Garsia-Lamperti, Erickson, Williamson, Doney 1997, Caravenna-Doney, Berger (both).
- Paper G does not cite: Baldassarri et al., the Akimoto papers, the teletraffic papers, Wang-Vezzani-Burioni-Barkai 2019.

## Source by source

### 1. Starreveld, Bekker, Mandjes (FULL: abstract, introduction, statements in Section 3)
- Occupation times of alternating renewal processes with Levy applications. J. Appl. Probab. 55 (2018), no. 4, 1287-1308. DOI 10.1017/jpr.2018.86. arXiv 1602.05131 (v2).
- Continuous time; sojourn times in the two sets may be dependent, which relaxes the independent alternating case of Takacs. Occupation time Phi(t) of the set A up to t.
- Proves: Prop. 3.1 (law of Phi(t) in terms of the joint law of the sojourns); Theorem 3.1 (transform of Phi(e_q), e_q exponential); Theorem 3.2 (CLT for Phi(t)/t under finite second moments; they say it generalizes Takacs 1957, Theorem 2); Theorem 3.3 (Gartner-Ellis: lim (1/t) log P(Phi(t) > qt) = -I(q), under a moment generating function finite near 0, so light tails); Theorem 3.4 and Props. 3.2, 3.3 (spectrally positive Levy processes reflected at the infimum).
- Their claim: "to the authors' knowledge large deviations asymptotics for occupation times have not been studied before in the literature" (introduction). It holds for the light-tailed setting; do not repeat it as a statement about heavy tails (see item 14).
- Relation: context and light-tailed analogue. No heavy tails, no infinite mean, nothing local. This is the standard applied-probability citation for the occupation time of an alternating renewal process. F lacks it; G has it.

### 2. Horii, Lefevere, Nemoto (FULL: abstract, introduction, Theorems 2.1 and 2.2, Section 4.2)
- Large time asymptotic of heavy tailed renewal processes. J. Stat. Phys. 186 (2022), article 11 (online 13 Dec 2021). DOI 10.1007/s10955-021-02856-5. arXiv 2106.03182 (v2).
- Object: counting process N_t of a renewal process with heavy-tailed waiting times, and the moment generating function M(t,h) = E exp(h N_t), h < 0.
- Theorem 2.1: for Pareto waiting times with integer exponent m at least 3, lim t^{m-1} M(t,h) = 1/(1 - e^h). Theorem 2.2: a summability bound (11) and an upper bound (12) on M. The proof uses Feller's one-big-jump result for P[S_k > t] at fixed k plus a dominated-convergence step.
- Everything else (non-integer Pareto, inverse Rayleigh, lognormal, the finite-time rate function) is numerical. The sentence "Mathematically justifying this asymptotic expression is an open problem" concerns the asymptotic form of the finite-time rate function in Section 4.2 (log P[N_t < xt] roughly log M_0(t) plus a log t term). The trivial lower bound P[N_t < xt] at least P[tau_1 > t] = M_0(t) is eq. (38).
- Relation: analogue in spirit (one big jump for a renewal counting process) but a different regime (tail index at least 2, integer Pareto), a different observable (number of renewals) and a different object (generating function, not mass function). Use only as motivation. Not an overlap.

### 3. Lefevere, Mariani, Zambotti (ABSTRACT)
- Large deviations for renewal processes. Stochastic Process. Appl. 121 (2011), no. 10, 2243-2271. DOI 10.1016/j.spa.2011.06.005. arXiv 1009.2659.
- Abstract: large deviations for the empirical measure of the forward and backward recurrence time processes of a classical renewal process with arbitrary waiting-time law; Donsker-Varadhan theory does not apply; the rate functional is non-strictly convex and non-analytic. Keywords include cumulative processes and heavy tails.
- Relation: context only. It is about the empirical measure of the age and residual-life processes, not occupation counts of an alternating process. I did not read its theorems. Verify before citing for more than "large deviations for renewal processes with heavy tails have singular rate functionals".

### 4. Heath, Resnick, Samorodnitsky (ABSTRACT)
- Heavy tails and long range dependence in on/off processes and associated fluid models. Math. Oper. Res. 23 (1998), no. 1, 145-165. DOI 10.1287/moor.23.1.145.
- Abstract: a stationary renewal process alternating active and inactive periods induces a stationary indicator process; heavy-tailed on periods give a slowly decaying covariance of the indicator (long range dependence); consequences for fluid models with constant input and release rates.
- Relation: context. Stationary version, covariance of the indicator, fluid buffer. Not the exact law of the occupation count at a fixed horizon. Read the paper before writing any sentence of the form "this paper does not give X".

### 5. Taqqu, Willinger, Sherman (ABSTRACT)
- Proof of a fundamental result in self-similar traffic modeling. ACM SIGCOMM Comput. Commun. Rev. 27 (1997), no. 2, 5-23. DOI 10.1145/263876.263879.
- Abstract: the superposition of many on/off sources with strictly alternating on and off periods and infinite variance in on or off periods can give self-similar (long-range dependent) aggregate traffic, with a simple relation between the Noah exponent (tail index) and the Joseph exponent (Hurst index); a Levy stable motion limit is also obtained.
- Relation: context. Many-source limit, not one source at a fixed horizon. This is the standard teletraffic citation.

### 6. Mikosch, Resnick, Rootzen, Stegeman (ABSTRACT)
- Is network traffic approximated by stable Levy motion or fractional Brownian motion? Ann. Appl. Probab. 12 (2002), no. 1, 23-68. DOI 10.1214/aoap/1015961155.
- Abstract: for the cumulative input of many heavy-tailed on/off sources, stable Levy motion is the approximation when connection rates are modest relative to the heavy tail of connection lengths, and fractional Brownian motion when rates are large; results are limit theorems for sequences of cumulative input processes whose rates vary to remove or induce long range dependence.
- Relation: context, same family as item 5. It concerns the order of limits (time and number of sources).

### 7. Godreche, Luck (FULL: abstract, introduction, Section 7 and parts of Section 3)
- Statistics of the occupation time of renewal processes. J. Stat. Phys. 104 (2001), no. 3-4, 489-524. DOI 10.1023/A:1010364003250. arXiv cond-mat/0010428.
- Continuous-time two-state process with independent intervals, one interval law for both states (they average over the initial sign). Three cases: narrow law, broad with alpha < 1, broad with 1 < alpha < 2. Method: Laplace transforms; physics-level derivations, no theorems.
- Section 7: the double Laplace transform of the occupation time T_t^+ and of S_t (eq. 7.2). For alpha < 1: the Lamperti law (7.10); the magnetization density f_M (7.6); its endpoint divergence (7.7); the critical index alpha_c = 0.594611... solving alpha_c = cos(pi alpha_c / 2), with the U to W change of shape, attributed to their reference [24] (Baldassarri et al.); a scaling form (7.11) in the persistence region whose scaling function h(z) is non-universal. For 1 < alpha < 2: eq. (7.12) gives a symmetric stable law of index alpha for S_t at scale t^{1/alpha}; moments (7.13) of order t^{3-alpha}, bifractal moment exponents; typical size t^{1/alpha}.
- They state that neither Lamperti nor their ref. [24] contains the scaling analysis for 1 < alpha < 2.
- Relation: overlap in the picture, not in the statements. Distributional, scaling-level, symmetric (one law for both states). No lattice mass function, no uniform error, no atoms or boundary layers beyond the scaling form. Already cited by F and G.

### 8. Baldassarri, Bouchaud, Dornic, Godreche (FULL: abstract and introduction only)
- Statistics of persistent events: an exactly soluble model. Phys. Rev. E 59 (1999), R20-R23. DOI 10.1103/PhysRevE.59.R20. arXiv cond-mat/9805212 (May 1998), titled "Generalized persistence exponents: an exactly soluble model".
- Spin flips separated by independent Levy-distributed intervals; the limit law of the mean magnetization and the generalized persistence exponents are obtained exactly.
- Relation: context for the U/W threshold remark. The attribution of the threshold rests on Godreche-Luck; I did not check the derivation here.

### 9. Akimoto, Sera, Yamato, Yano (FULL: abstract, introduction, statements of Theorems 1 and 2)
- Aging arcsine law in Brownian motion and its generalization. Phys. Rev. E 102 (2020), 032103. DOI 10.1103/PhysRevE.102.032103. arXiv 2004.00808.
- Theorem 1: for Brownian motion, the law of the fraction of time spent positive over the window [t_a, t_a + t_m] depends on t_a / t_m only (explicit aged arcsine law). Theorem 2: for a two-state renewal process with power-law sojourn times of index in (0,1), with t_a / t_m = r fixed as t_m grows, the occupation fraction converges in law to an aged generalized arcsine law (Lamperti law at r = 0). Proofs are in Appendices A and B.
- Relation: this is the distributional aging law for 0 < alpha < 1 that stretch A of the plan would localize. A local version is not in the paper. The title has no "renewal", so cite by the exact title.

### 10. Akimoto 2023 (FULL: abstract, skim)
- Statistics of the number of renewals, occupation times, and correlation in ordinary, equilibrium, and aging alternating renewal processes. Phys. Rev. E 108 (2023), 054113. DOI 10.1103/PhysRevE.108.054113. arXiv 2306.00359. Single author. Already in F.
- Moments of the number of renewals and of the occupation time for case studies; anomalous fluctuations when the second moment diverges; Mittag-Leffler and generalized arcsine laws, with aging, when the mean diverges. Distribution and moment level; nothing local.

### 11. Barbe, McCormick (FULL: abstract, table of contents, introduction; theorems and proofs not read)
- Asymptotic expansions for infinite weighted convolutions of heavy tail distributions and applications. Mem. Amer. Math. Soc. 197 (2009), no. 922. DOI 10.1090/memo/0922. arXiv math/0412537.
- Main result (Section 2.3, Theorem 2.3.1 in the arXiv text): asymptotic expansions for the tail of infinite weighted convolutions of laws with regularly varying tails. Applications (Section 4): ARMA models, tail index estimation, randomly weighted sums, randomly stopped sums, queueing, branching, infinitely divisible laws, implicit transient renewal equations (4.8). The introduction places it relative to Chover et al. 1973 and Grubel 1987 for transient renewal measures.
- Relation: technique and credit (tails of compound sums, transient renewal), not occupation times. I could not tell from this reading which of its theorems the plan's "Barbe-McCormick credit" refers to; the author must name it.

### 12. Lamperti 1958 and Mitov-Yanev 2001
- Lamperti: An occupation time theorem for a class of stochastic processes. Trans. Amer. Math. Soc. 88 (1958), 380-387. DOI 10.1090/S0002-9947-1958-0094863-X. (Classical; not re-read.) Generalized arcsine law for A_N / N with cycle tails regularly varying of index in (0,1). In both papers.
- Mitov, Yanev: Limit theorems for alternating renewal processes in the infinite mean case. Adv. in Appl. Probab. 33 (2001), no. 4, 896-911. DOI 10.1239/aap/1011994035. (ABSTRACT.) Abstract: the asymptotic behaviour of an occupation-time process of alternating renewal processes in the infinite mean cycle case; the limit theorems extend results of Dynkin (1955), Lamperti (1958) and Erickson (1970) for the spent lifetime process; "some new phenomena". Distributional. In G, not in F.

### 13. Caravenna-Doney, Doney 1997, Berger
- Caravenna, Doney: Local large deviations and the strong renewal theorem. Electron. J. Probab. 24 (2019), paper 72, 48 pp. DOI 10.1214/19-EJP319. arXiv 1612.07635. (Abstract read.) Local large deviation upper bound for random walks in the domain of attraction of an alpha-stable law, alpha in (0,1) and (1,2); for alpha in (0,1), necessary and sufficient conditions for the strong renewal theorem. Already in both.
- Doney: One-sided local large deviation and renewal theorems in the case of infinite mean. Probab. Theory Related Fields 107 (1997), no. 4, 451-465. DOI 10.1007/s004400050093. (Journal record only.) In G, not in F.
- Berger: Notes on random walks in the Cauchy domain of attraction. Probab. Theory Related Fields 175 (2019), no. 1-2, 1-44. DOI 10.1007/s00440-018-0887-0. arXiv 1706.07924. (Abstract read.) Fuk-Nagaev inequality and a local version; a large deviation theorem; two local large deviation theorems; applications to ladder epochs and renewal theorems; most techniques carry to alpha in (0,2). Input for the boundary case alpha = 1.

### 14. Wang-Schulz-Deng-Barkai 2018; Wang-Vezzani-Burioni-Barkai 2019
- Wang, Schulz, Deng, Barkai: Renewal theory with fat-tailed distributed sojourn times: typical versus rare. Phys. Rev. E 98 (2018), 042139. DOI 10.1103/PhysRevE.98.042139. arXiv 1809.05856. (FULL: abstract, introduction, Section VII.) Continuous time; large deviations of the number of renewals, the recurrence times and the occupation time, via non-normalized (infinite) densities and the big jump principle. Section VII.A (alpha < 1): an atom for the occupation of the initial state and an infinite density (eqs. 70-76). Section VII.B (1 < alpha < 2): the typical stable law and a non-normalized density for rare events (eq. 83) that depends on the interval law only through alpha and an amplitude b and is not integrable at the endpoint. Simulations; no error terms. This is the closest prior work to F's big-jump theorem and G's end layers: formal, continuous time, no uniform statement. It also answers the quote in item 1: heavy-tailed occupation-time large deviations were treated, formally, in 2018.
- Wang, Vezzani, Burioni, Barkai: Transport in disordered systems: the single big jump approach. Phys. Rev. Research 1 (2019), 033172. DOI 10.1103/PhysRevResearch.1.033172. arXiv 1906.04249. (FULL: abstract only; I did not find an occupation-time section.) Biased continuous-time random walk; the largest trapping time controls rare fluctuations; the initial condition persists in the rare fluctuations. Context for aging plus big jump.

### 15. Zaburdaev, Denisov, Klafter
- Levy walks. Rev. Mod. Phys. 87 (2015), 483-530. DOI 10.1103/RevModPhys.87.483. (Journal record; the section and figure F cites were not re-checked.) Review; context.

## 2023-2026 search

Method: web searches and Crossref lookups on 2026-10-26. The arXiv listing API returned nothing, so the search is not exhaustive. I found no paper that proves a local limit theorem or a big-jump / large deviation law for the occupation count of an alternating renewal process or a lattice Levy walk with regularly varying tails. Related hits:

- Akimoto, PRE 108, 054113 (2023): moments and distributional limits with aging. Already in F.
- Dessertaine, Godreche, Bouchaud: Occupation time of a renewal process coupled to a discrete Markov chain, arXiv 2204.11228 (v2, May 2022; journal not checked): Lamperti law for semi-Markov processes, Laplace-space formula, finite-time corrections to moments.
- Plaud, Benichou: Beyond the arcsine law: exact two-time statistics of the occupation time in jump processes, arXiv 2510.25859 (Oct 2025): joint law of occupation time and position, aged occupation-time law, autocorrelation, by Wiener-Hopf methods. Aging, distributional.
- Akimoto: Statistics of a large number of renewals in equilibrium and ordinary renewal processes at the short time limit, Chaos 36 (2026), DOI 10.1063/5.0324747 (title only).
- Berger, Birkner, Yuan, Ann. Fac. Sci. Toulouse 33 (2024); Doney, EJP 28 (2023); Melbourne, Pene, Terhesiu, arXiv 2610.15720 (2026): all already cited by F.
- Bassanoni, Vezzani, Burioni: extreme value statistics for Levy flights, Levy walks and the Levy-Lorentz gas, Chaos (2024): physics, numerical confirmation (summary only).
- A Crossref record "Large-time asymptotics of anomalous fluctuations in heavy-tailed renewal-reward processes" (Universite Paris Cite, DOI 10.70675/e62613eaz118cz4f85zbfedz421219b44c54): looks like a follow-up or thesis connected to Horii-Lefevere-Nemoto. Not opened. Check it, since it may prove what the 2021 paper called open.
- Kevei, Terhesiu: strong renewal theorem with infinite mean beyond regular variation, J. Theoret. Probab. 35 (2022) (title only).
- Wang, Chen, Deng: Aging two-state process with Levy walk and Brownian motion, arXiv 1906.03023 (2019); Schulz, Barkai, Metzler: Aging renewal theory and application to random walks, Phys. Rev. X 4 (2014), 011028, DOI 10.1103/PhysRevX.4.011028: aging background for the initial-run theorem.

## Positioning summary

The merged paper sits between four literatures.

1. Renewal theory. The occupation time of an alternating renewal process is classical in distribution (Takacs; Lamperti; Mitov-Yanev; Starreveld-Bekker-Mandjes for light tails). The local theory rests on strong renewal theorems (Garsia-Lamperti, Erickson, Doney, Caravenna-Doney).
2. Heavy-tailed random walks: local limit theorems, local large deviations and big-jump domains (Nagaev, Rozovskii, Denisov-Dieker-Shneer, Caravenna-Doney, Berger, Berger-Birkner-Yuan). The window theorem is the occupation-count version.
3. Teletraffic and queueing on/off models (Heath-Resnick-Samorodnitsky, Taqqu-Willinger-Sherman, Mikosch-Resnick-Rootzen-Stegeman). They study the stationary indicator and superpositions of many sources. The exact law of one source's occupation count at a fixed horizon, with initial run and atoms, is not their object. This rests on abstracts.
4. Statistical physics of Levy walks and aging (Godreche-Luck, Baldassarri et al., Zaburdaev-Denisov-Klafter, Wang et al. 2018 and 2019, Akimoto et al. 2020, Akimoto 2023). The picture (stable bulk, infinite density in the tails, aging) is known at the level of Laplace transforms and scaling. No theorems with uniform errors on the lattice.

Sentences the introduction must contain:

- "The limiting law of the occupation time of an alternating renewal process is classical: the generalized arcsine law of Lamperti for 0 < alpha < 1 (also Mitov-Yanev), a stable law at scale N^{1/alpha} for 1 < alpha < 2 (Godreche-Luck, at physics level), and a CLT and a light-tailed large deviation principle under finite variance or exponential moments (Starreveld-Bekker-Mandjes). These are statements about distribution functions. We give the mass function at every lattice point."
- "In physics the rare-event regime is described by non-normalizable densities and the single big jump principle (Wang et al. 2018, 2019; Vezzani et al. 2019, 2020; Rebenshtok et al. 2014), formally, in continuous time and without error terms. We prove the lattice statement with uniform errors, with the boundary layers and the endpoint atoms, and we show how the initial run enters each piece."
- "For 0 < alpha < 1 the local Lamperti law at one point holds if and only if the strong renewal theorem holds for both run laws. For alpha above 1/2 this is automatic (Garsia-Lamperti, Erickson); below 1/2 the criterion is that of Caravenna-Doney. The equivalence with the occupation law is ours."
- "The on/off teletraffic literature (Heath-Resnick-Samorodnitsky; Taqqu-Willinger-Sherman; Mikosch et al.) uses heavy-tailed on/off sources through long-range dependence of the stationary indicator and limits of many sources. We treat one source at a fixed horizon and give the sampling law of the utilization A_N / N exactly, including its dependence on the starting point. The aging limit is distributional only (Akimoto et al. 2020)."

## Cautions

- Do not write that large deviations of occupation times are unstudied. That is Starreveld et al.'s claim for the light-tailed case; Wang et al. 2018 do the heavy-tailed case formally.
- Do not call one-big-jump for renewal counts "open" without saying it is the Horii-Lefevere-Nemoto statement about the finite-time rate function at tail index 2 or more, and check the possible follow-up first.
- A local aging law is new only if none exists; none was found, but the search was not exhaustive.
- Not read beyond abstracts: Heath-Resnick-Samorodnitsky, Taqqu-Willinger-Sherman, Mikosch et al., Lefevere-Mariani-Zambotti, Doney 1997, Lamperti 1958, Mitov-Yanev. Theorems not read: Barbe-McCormick. Not re-opened: Zaburdaev et al.
