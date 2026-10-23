# Paper F: feasibility and novelty of a shorter lattice Lévy walk paper

Research date: October 22, 2026 (America/Los_Angeles). Initial targeted assessment. Research notes only: no manuscript edits, commits, Lake runs, simulations, or long numerical sweeps.

The required researcher instructions were read first. Local inputs include paperF/sec_heavy.tex, app_heavy.tex, sec_intro.tex, problem131_heavy_aging.tex; reports/Paper F literature and review.md; the earlier renewal, persistent-walk, Lévy-walk, synthesis, and aging notes; and the locally saved DLS and Engländer–Volkov draft extracts. Earlier conclusions are leads, not independent verification of new claims. The October 18 review predates changes now visible in the manuscript; several credit corrections it recommends are already present.

Access discipline: primary-source browser searches were performed independently. Relevant passages were inspected in browser-extracted primary PDFs or HTML; this is not a claim to have read every page of those papers. Existing local source texts were also consulted. A direct shell download of Caravenna–Doney failed because the host could not resolve arxiv.org; no downloaded PDF is claimed. The browser-source capture in 01_F_evidence is a partial tool-response record, not a full-source archive. Existing PDFs/text stay local. Published-book numbering, paywalled sources, and exhaustive database coverage remain unchecked.

## 1. What can safely be proved, and what needs correction?

### Takeaway

The fixed-exponent extension to general slowly varying tails is mathematically feasible. For 1 < α < 2, a weaker local large-deviation estimate suffices to extend the center theorem even without regular variation of the individual masses. The proposed logarithmic exponent βφ is correct, but the multiplier is generally not the current C(φ). A moving α window requires a separate uniform theorem.

### Cited Findings

The primary external ingredients actually checked are:

- **Caravenna–Doney, local upper bound:** arXiv:1612.07635v3, Theorem 1.1, especially Eq. (1.6), pp. 1–2: for a stable domain of attraction with α in (0,1) or (1,2), positive right-tail coefficient, and zero mean when α > 1, a bounded-interval probability is at most a constant times n/[a_n A(x)]. Their hypotheses do not require regular variation of point masses. Section 2, Eqs. (2.1)–(2.7), supplies the norming framework, Potter bounds, Karamata sums, and local-limit estimates. [Primary PDF](https://arxiv.org/pdf/1612.07635v3).
- **Berger, stronger local estimate:** arXiv:1706.07924v4, Theorem 2.4, Eqs. (2.5), (2.7), (2.9), (2.10), printed p. 4: a local mass upper bound gives the sharper n L(x)x^(-1-α) estimate; regular variation of the mass gives a local big-jump equivalence. Theorem 2.3 gives the weaker bound without that mass hypothesis. This directly corrects the unverified “Theorem 2.7” locator carried in the old renewal notes: in the version inspected here the useful theorem is **2.4**, not 2.7. [Primary PDF](https://arxiv.org/pdf/1706.07924v4).
- **The current decomposition is exact:** Proposition prop:tworenewal and Eq. eq:C-conv express the center as a sum of products of two independent renewal quantities. Proposition prop:C-center then uses F1–F3 and four regions of the renewal index. These are the local manuscript premises of the derivation below. [sec_heavy.tex](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/paperF/sec_heavy.tex>), [app_heavy.tex](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/paperF/app_heavy.tex>).

### Inferences

The following is an independent derivation and proposed theorem package. These conclusions are not attributed as statements already appearing in the sources above.

#### 1.1 Conventions: run survival, residual survival, mass, and lattice factor

Write

    T(k) = P(ξ ≥ k) ~ k^(-α) L(k),     1 < α < 2,
    μ = Eξ = Σ_{k≥1} T(k).

Here L is positive and slowly varying; any tail amplitude is included in L. Assume ξ is positive integer valued with maximal lattice span 1. A regularly varying mass,

    p(k) ~ α k^(-α-1) L(k),

is a sufficient stronger assumption, but is not implied by survival regular variation alone. In particular, one cannot obtain a pointwise difference asymptotic simply by differentiating an arbitrary regularly varying sequence.

The phrase “stationary run tail” must not conflate T with the stationary first-run tail. For the stationary start,

    P(D = j) = T(j)/μ,
    P(D ≥ N) = μ^(-1) Σ_{j≥N} T(j)
              ~ N^(1-α)L(N)/[(α-1)μ].

Thus the stationary first run has tail index α−1. Throughout these notes E_N means **one endpoint**, not the sum of both endpoints:

    E_N^stat ~ N^(1-α)L(N)/[2(α-1)μ],
    E_N^fresh = T(N)/2.

Both formulas follow from the first-run persistence event; the sum asymptotic follows by applying the Karamata tail-sum formula cited above. Multiplying by 2 for both ends would change every comparison constant.

Also A_N has mesh 1, whereas S_N = 2A_N−N has mesh 2. A continuum density for S_N must be multiplied by 2 when predicting P(A_N=N/2). No distributional convergence alone justifies that prediction.

#### 1.2 Norming: define an inverse, not a guessed slowly varying multiplier

Choose a positive, ultimately increasing norming a(t) satisfying

    t T(a(t)) → 1,
    a(t)^α / L(a(t)) ~ t.

Use a stepwise extension of T to real arguments if needed. Equivalently, a is an asymptotic inverse of H(x)=x^α/L(x), and a belongs to RV(1/α). Replacing a by an equivalent monotone representative is harmless. Put

    b_h = a(h/μ),        h=N/2.

This convention absorbs the entire survival-tail amplitude into a. The associated centered stable variable has characteristic function

    E exp(itG_α) = exp[K_α(-it)^α],
    K_α = -Γ(1−α) = Γ(2−α)/(α−1).

In particular the stable scale is NOT also absorbed a second time into a. With

    σ_α = 2K_α |cos(πα/2)|,
    I_α = ∫ g_α(x)^2 dx
        = Γ(1+1/α)/(π σ_α^(1/α)),

the candidate center asymptotic is

    C_N ~ 2 I_α / a(N/(2μ)).                                  (F1*)

The last identity for I_α follows directly from Plancherel, as in Lemma lem:stable(iv). The factor 2 in σ_α comes from taking the difference of two independent stable sums; the factor 2 in C_N comes from the two terms in the renewal identity. Keeping both factors is essential.

A de Bruijn-conjugate description is possible: set ℓ(x)=L(x)^(-1/α) and let ℓ# satisfy ℓ(x)ℓ#(xℓ(x))→1 and its reciprocal conjugacy relation. Then

    a(t) ~ t^(1/α) ℓ#(t^(1/α)).

The implicit inverse definition is safer for the paper and sufficient for every conclusion here; the conjugate formula is algebraic explanatory notation, not a separately source-verified theorem locator.

**Why evaluation at N is generally wrong.** For L(x)=exp(sqrt(log x)), the equation H(a)=t can be solved exactly after setting z=sqrt(log a):

    αz²−z=log t,
    z=[1+sqrt(1+4α log t)]/(2α).

Consequently

    a(t) ~ exp[1/(2α²)] t^(1/α)
           exp[α^(-3/2)sqrt(log t)].

The guess t^(1/α)L(t)^(1/α) gets even the coefficient of sqrt(log t) wrong. The better guess t^(1/α)L(t^(1/α))^(1/α) still misses the nontrivial constant exp[1/(2α²)]. This is a direct calculation, illustrating why the inverse must be retained for unrestricted L.

#### 1.3 Safe candidate theorem and proof reduction

**Candidate theorem, fixed law.** Let ξ be positive integer valued, of maximal span 1, with T(k)~k^(-α)L(k), 1<α<2. Let the first direction be fair. Let D, independent of the later i.i.d. runs and the initial direction, be any almost surely finite positive integer valued variable. Define a as above. Then, along even N, (F1*) holds. For the stationary start,

    R_N ~ N^(1−α)L(N) a(N/(2μ)) / [4(α−1)μ I_α].              (F2*)

For the fresh start,

    R_N ~ N^(−α)L(N) a(N/(2μ)) / (4 I_α).                    (F3*)

No moment condition on D is required. The theorem is for each fixed run law and each fixed law of D; it does not assert uniformity over arbitrary changing laws.

**Status:** the reduction below closes the specific obstruction in the existing appendix at the level of detailed research notes. It has not been incorporated into the manuscript or independently refereed. It should receive a fresh line-by-line proof check before being described as a completed extension.

Here is the needed proof, including the difficult discarded region.

1. Stable attraction with tT(a(t))→1 gives the stated G_α. The maximal-span lattice LLT gives

       sup_k |a_m u_m(k)−g_α((k−mμ)/a_m)| → 0,
       sup_{m,k} a_m u_m(k) < ∞.

   This is the same LLT used in the manuscript; it also appears in Caravenna–Doney §2.3, Eq. (2.6), and Berger §1, Eq. (1.4). One must use the lattice span, not merely the gcd of the support without considering translations.

2. Replace F1 by an ultimately increasing a in RV(1/α). The needed properties are a_m/a_(m−1)→1, b_h=o(h), a(ch)/a(h)→c^(1/α), and a_m/b_h→1 uniformly for |mμ−h|≤M b_h. Regular variation supplies all of them. Negative logarithmic powers and oscillatory slowly varying factors are therefore allowed; the current restriction β≥0 has no intrinsic role.

3. Lemma lem:C-firstpassage uses only this adjacent-index property, the LLT bound, and summability of T and P(D=·). Its truncation argument continues to work. It gives the three delayed/covering local approximations with coefficients 1, μ, μ. Almost-sure finiteness of D is enough because P(D>J)→0; finite E[D] is unnecessary.

4. **Replacement for F3 in the early region.** Apply Caravenna–Doney Eq. (1.6) to X=ξ−μ. Its mean is zero, its positive tail is equivalent to T(x), and its negative tail is eventually zero. For m≤h/(4μ), x=h−mμ is at least 3h/4. A fixed interval of length 1 isolates the desired lattice point. Therefore

       u_m(h) ≤ C (m/a_m) T(h).

   Since m/a_m belongs to RV(1−1/α) with positive index, Potter bounds yield

       sup_{1≤m≤c h} m/a_m ≤ C h/a(h).

   Finite small values of m are included by enlarging C; h/a(h)→∞. Thus

       sup_{m≤h/(4μ)} u_m(h) ≤ C [h/a(h)]T(h).

   Split q_m(h)=Σ_j T(j)u_(m−1)(h−j) at j=h/2. The j≥h/2 part is at most CT(h), using monotonicity and regular variation of T. For j<h/2 and m≥2,

       (h−j)−(m−1)μ ≥ h/4,

   so the same estimate applies; its T(j) weights sum to at most μ. The case m=1 is q_1(h)=T(h). Hence

       sup_{m≤h/(4μ)} q_m(h)
           ≤ C [1+h/a(h)] T(h).

   Now use Σ_m q^D_(m+1)(h)≤1 and Σ_m u^D_m(h)≤1 in the exact two-renewal identity. Its early-region sum Σ_1 satisfies

       b_h Σ_1 ≤ C [a(h)+h] T(h) → 0,

   because a(h)=o(h) and hT(h) belongs to RV(1−α), a negative index.

   This is the decisive observation: the stronger m p(h) estimate is convenient but unnecessary here. A regular-mass assumption is sufficient, yet avoidable for this finite-mean center theorem.

5. In the remaining two outer regions, monotonicity and regular variation give u_m(h),u^D_m(h)≤C/b_h. The other factors sum to upper or lower tails of τ_m, plus P(D≥b_h). Stable convergence and almost-sure finiteness of D discard them as M→∞.

6. In |mμ−h|≤M b_h, the product equals

       (2μ/a_m²)[g_α((h−mμ)/a_m)²+o(1)]

   uniformly over that window. There are O(b_h) terms. Substitution y=(h−mμ)/b_h has mesh μ/b_h, yielding

       b_h Σ_3 → 2∫_{−M}^M g_α(y)²dy.

   Let M→∞. This proves (F1*), after which the endpoint identities prove (F2*) and (F3*).

For a deliberately conservative first draft, the theorem may assume p(k)~αk^(-α-1)L(k) and use Berger Theorem 2.4 for Step 4. But that restriction should be described as a presentation choice, not a mathematical necessity shown by this audit.

#### 1.4 Correct logarithmic constant

Suppose more specifically

    T(k) ~ A k^(−α)(log k)^β,       A>0, β real.

This is an asymptotic assumption: an actual monotone survival function must be specified at small k. The literal formula at k=1 is not a probability tail for general β. Using log(ek), or specifying the tail only after a cutoff, repairs that issue but changes μ.

Solving the norming equation gives

    a(t) ~ A^(1/α) α^(−β/α) t^(1/α)(log t)^(β/α).

Indeed log a(t)~(log t)/α, and the α^(−β) from (log a)^β must be compensated in a^α. Therefore

    C_N ~ 2I_α A^(−1/α) α^(β/α)
           (2μ/N)^(1/α)(log N)^(−β/α),

    R_N^stat ~ D_(α,β,A,μ)
                N^(1−α+1/α)(log N)^[β(1+1/α)],

    D_(α,β,A,μ)
       = A^(1+1/α) α^(−β/α)
           / [4(α−1)μ(2μ)^(1/α)I_α]
       = C_pure(α) A^(1+1/α) α^(−β/α)
           [ζ(α)/μ]^(1+1/α).

Here C_pure is precisely the current manuscript's C(α), for T(k)=k^(-α) at every k. At φ:

    R_N^stat ~
       C_pure(φ) A^φ φ^(−β/φ)[ζ(φ)/μ]^φ (log N)^(βφ).        (F4*)

Thus the proposed exponent βφ is right. The proposed unchanged C(φ) is generally wrong. It omits both the inverse-norming factor and the changed mean, and also the amplitude if A≠1.

Consequences:

- β>0: endpoints eventually beat the center at α=φ.
- β<0: the center eventually beats an endpoint at α=φ.
- β=0: the answer is decided by the full constant; tail index alone does not decide it.
- The current strict C_pure(φ)<1 is a fact about the exact pure-power model, not a universal property of the entire regularly varying class.

The last point remains true with A=1. Altering finitely many tail values changes μ without changing the asymptotic tail. For example, set T(1)=1, T(k)=K^(-α) for 2≤k<K, and T(k)=k^(-α) for k≥K. This is a valid span-1 law with μ→1 as K→∞. At φ its critical constant tends to C_pure(φ)ζ(φ)^φ, which is greater than 1. Increasing the body mean sufficiently gives the opposite comparison. The effect is intrinsic equilibrium sampling, not an error in the old pure-power constant.

For unrestricted L, retain (F2*). Away from φ the index e(α)=1−α+1/α determines the sign because the remaining factor is slowly varying. At φ it is a slowly varying factor involving both L(N) and the inverse a(N/(2μ)); it may grow, vanish, or oscillate. There is no universal replacement by L(N)^φ.

#### 1.5 Finite-size α window: correct conditional statement

For the exact pure-power family, put

    d = −e'(φ) = 1+φ^(−2) = 1.38196601125… .

If the center asymptotic is proved uniformly for α in a compact neighborhood of φ, then for bounded κ,

    α=φ−κ/log N   ⇒
    R_N(α) → C_pure(φ) exp(dκ).

The limiting tie occurs at

    κ_* = −log C_pure(φ)/d = 0.1833858634… .

This scalar evaluation uses the existing manuscript value C_pure(φ)=0.7761317206…, not a numerical sweep.

This is NOT justified by substituting α_N into a pointwise asymptotic. The uniform proof must cover the lattice LLT, delayed kernels, discarded regions, and stationary first run. For the pure-power family a plausible short route is:

1. Make the polylogarithm characteristic-function expansion uniform on a compact J⊂(1,2).
2. Use continuous dependence on α and uniform positive masses at 1 and 2 for a uniform Fourier contraction away from zero.
3. Obtain uniform small-frequency stable domination and hence the LLT by Fourier inversion.
4. Use one sufficiently large truncation constant r for the current Chernoff proof for every α∈J; all truncated-moment constants can be chosen uniformly because J avoids 1 and 2.
5. Use uniform tightness of the stationary D_α, from a bound C t^(1−min J).

This is a proposed proof program, not a completed uniform theorem. An o(1) uniform relative error is enough for the leading 1/log N window; a quantitative rate is not necessary for that leading coefficient.

Continuity plus a uniform limit gives existence of a crossing in the shrinking bracket and the leading location for roots in that bracket. It does **not** by itself give uniqueness, global monotonicity in α, or a global finite-N crossing theorem.

For the logarithmic family with fixed β and a suitably uniform smooth choice of body law, the predicted crossing changes to

    α_N = φ + [βφ log log N + log D_(φ,β,A,μ_φ)]
                  /(d log N) + o(1/log N).

Thus β≠0 generally changes the window's center by order log log N/log N. An unrestricted collection of slowly varying L has no automatic uniformity; even the small-k body law can vary badly with α.

#### 1.6 Appendix audit: what survives, what must change

- **F1 is genuinely restrictive as written.** It explicitly requires c x^κ(log x)^β with β≥0. It does not cover negative β, much less arbitrary L. Replace it and all uses of literal monotonicity by the equivalent increasing regular-variation framework.
- **F2 is the right local hypothesis.** Stable convergence alone is insufficient. Verify maximal span 1 and the chosen stable normalization.
- **F3 is a stronger local statement than tail regular variation.** Keep its proof for the exact pure-power law, replace it by Berger under a mass assumption, or use Step 4 above for the finite-mean theorem.
- **The delay argument is sound for fixed a.s. finite D.** There is no need to impose E[D]<∞; the stationary residual mean actually diverges for the main 1<α<2 regime.
- **The four-region proof does not appear to hide a fatal pure-power gap.** The main error bookkeeping works because the LLT error is uniform and there are O(b_h) main terms. This is a targeted independent audit, not a certification of every formula in the entire paper.
- **Infinite-mean case is different.** Lemma lem:C-stable1(iii) uses a genuinely local bound. Generalizing it with Berger requires the mass upper condition (2.5), which regular varying mass certainly implies. The weaker Caravenna–Doney estimate is not interchangeable with it in the existing α<1 small-m argument, because m/a_m then has negative rather than positive index.
- **The local Lamperti proof for the present pure law is worth keeping.** In the main range it establishes m q_m(h)≈t g(t)/α, then integrates u_m(h)[q_m(h)+q_(m+1)(h)] in log m. The positive stable ratio identifies the center constant 2tan(πα/2)/π. Its pointwise statement is stronger than weak Lamperti convergence.
- **Do not claim all-L local Lamperti yet.** With regular mass it looks feasible using a_m~inverse of 1/T, Potter bounds for T(ja_m)/T(a_m), and a Stieltjes/Riemann-sum argument replacing the exact identity log m=α log(h/t_m). Those replacement arguments have not been written out here.
- **α=1 stays outside the theorem.** In the general class, even finite versus infinite mean at α=1 depends on Σ L(k)/k. The current pure-power Cauchy heuristic is not a theorem for arbitrary L.
- **α=2 is not always a logarithmic-variance case.** Under a general tail k^(-2)L(k), the second moment may be finite or infinite; the normal-domain norming is set by the truncated second moment, not universally sqrt(m log m). This is a reason to demote that range rather than silently generalize the existing formula.

### Gaps

The new fixed-law theorem needs a clean formal write-up and an independent proof check. The moving-α theorem, uniqueness of crossings, rates, and an all-L infinite-mean local theorem are not proved in these notes. The possible weaker hypotheses for local Lamperti should not be guessed from strong-renewal theory; that is a separate question.

## 2. Is the proposed paper new relative to the nearest primary literature?

### Takeaway

The golden-ratio balance, stable bulk constant, equilibrium endpoint scaling, and Lamperti distribution are already in the literature. The defensible contribution is a rigorous lattice local theorem with an arbitrary finite first run, its exact endpoint comparison, and the way slowly varying tails resolve or destabilize the critical balance. I did not locate an identical theorem in the targeted search, but this is a provisional novelty assessment.

### Cited Findings

| Primary source and exact locator | What was checked and what it means |
|---|---|
| Wang–Li–Hänggi, book chapter §6.2.1.3, Eq. (6.49), printed pp. 267–268, especially the paragraph on p. 268. [Author-hosted chapter](https://www.physik.uni-augsburg.de/theo1/hanggi/Papers/678.pdf); [arXiv record](https://arxiv.org/abs/1512.07717). | The chapter explicitly balances central and side-peak heights and obtains φ. That observation must be credited; it cannot be the new theorem's discovery claim. The book locator was checked directly, avoiding confusion with arXiv's §2.1.3/Eq. (49). |
| Godrèche–Luck, arXiv:cond-mat/0010428v1, §7(iii), Eqs. (7.12)–(7.15), printed pp. 19–20; §7(ii), Eq. (7.10); equilibrium persistence Eq. (8.7). [Primary PDF](https://arxiv.org/pdf/cond-mat/0010428v1). | Transform analysis gives the continuous-time stable bulk with its coefficient, and the Lamperti density. The bulk coefficient reproduces F's pure-power central coefficient after the mesh-2 correction. The fresh-start bulk calculation and equilibrium persistence are different statements; they must not be merged into a claimed lattice LLT. |
| Cénac–Le Ny–de Loynes–Offret, arXiv:1612.00238v1, Theorem 3.2 and Eqs. (3.8)–(3.10); Theorem 3.3 and Eq. (3.25); §4.1 Eq. (4.1). [Primary PDF](https://arxiv.org/pdf/1612.00238v1). | Functional scaling limits cover general stable attraction, including slowly varying normalizations and the Lamperti marginal. Thus general L at the distributional level is already covered. A functional limit with an explicit density is not automatically convergence of individual lattice probabilities. Published numbering was not checked. |
| Denisov–Dieker–Shneer, arXiv:math/0703265v3, §9.1, Proposition 9.1 with Eqs. (25)–(27), Theorem 9.1; also Theorem 2.1. [Primary PDF](https://arxiv.org/pdf/math/0703265). | The work treats global and local big-jump domains with explicit tail regularity, centering, and domain requirements. It is background for a local deviation lemma, not by itself a theorem about this walk's occupation probability. Cite the matching result rather than applying a global tail estimate to a point event. |
| Doney 1997, abstract/introduction of author-uploaded paper, DOI 10.1007/s004400050093. [Author-uploaded primary text](https://www.researchgate.net/publication/226773936_One-sided_local_large_deviation_and_renewal_theorems_in_the_case_of_infinite_mean). | The inspected scope is α∈(0,1) and infinite mean. It is inappropriate as the sole citation for F's finite-mean α>1 lemma. Its exact theorem hypotheses were not audited here; use the directly inspected Berger theorem for a precise applicable locator. |
| Akimoto, arXiv:2306.00359v1, §V.A.1–2 in the PDF / §V.1.1–2 in HTML; equilibrium transform Eqs. (106)–(108) in HTML. [Primary HTML](https://arxiv.org/html/2306.00359v1); [primary PDF](https://arxiv.org/pdf/2306.00359). | A closer recent comparator studies ordinary, equilibrium, and aging alternating renewal occupation laws. It derives generalized-arcsine limits and equilibrium transforms. No matching lattice local theorem was located in the inspected sections; searching its PDF for “local limit” returned no match. Equation numbering differs between the returned HTML and PDF: use section headings unless fixing one version. |
| Dietz–Lippitt–Sethuraman, arXiv:1901.08135v1, §2.4, Theorem 2.18 and Eq. (2.15), printed pp. 15–16. [Primary PDF](https://arxiv.org/pdf/1901.08135v1). | The finite count law is recovered from limiting occupation moments of a resolvent-kernel chain. This is substantial prior art for the urn/count portion. The theorem is not a statement that the full path laws coincide. The old review's optimism about aging novelty should be read in light of this precise overlap. |
| Engländer–Volkov, March 18, 2024 author draft, Chapter 7, Claim 7.1, Theorem 7.2, and Lemma 7.1/Eq. (7.2). Local extracts are in Final probability papers review/evidence/03_DEF/ev_draft_pdfp149.txt through ev_draft_pdfp155.txt; Theorem 7.2 begins on PDF page 155, printed p. 139. [Dated author upload](https://www.researchgate.net/publication/379333206_Coin-Turning_Random_Walks_and_Inhomogeneous_Markov_Chains). | The inspected local draft material gives the two-state joint-law/mimicking comparison and urn cases. These are draft locators, not verified published-edition locators. Together with DLS they support dropping the aging half for focus; they do not justify saying every remaining aging statement is already known. |

The current introduction already credits Godrèche–Luck's bulk coefficient, Cénac et al.'s functional limits, WLH's heuristic, and the DLS/draft overlap. Any revision should preserve that credit rather than revert to stronger novelty language.

### Inferences

#### 2.1 The nearest overlap, stated fairly

Godrèche–Luck obtain, in their notation,

    S_t=(ct)^(1/α)X_t,    E exp(iuX)=exp(−|u|^α),
    c=K_α |cos(πα/2)| / μ

for unit pure-power tail amplitude. Its density at zero is Γ(1+1/α)/(π(ct)^(1/α)). Multiplying by the lattice mesh 2 gives exactly F's current central coefficient. This calculation is an independent comparison of the cited formulas, not a claim that GL proved the lattice point asymptotic. F's theorem supplies the missing local justification and handles independent arbitrary a.s. finite D.

Cénac et al. are even nearer to a general-L formulation because they use stable attraction and slowly varying normalizations already. Therefore:

- “General slowly varying Lévy-walk scaling” is not a viable novelty claim.
- “Golden ratio discovered for Lévy walks” is not viable.
- “First explicit stable central constant” is not viable.
- A safe claim is a direct lattice local result under precise tail hypotheses, with a delayed first run and an explicit persistence-to-center comparison.
- The logarithmic corollary is a useful, transparent consequence of the local theorem; it is unlikely to carry a substantial probability paper on its own.

The old review identifies directionally reinforced random walks (Mauldin–Monticino–von Weizsäcker; Horváth–Shao) and additive/regenerative LLTs as further overlap risks. Their full texts were not independently acquired in this pass. They remain unresolved rather than being declared absent. A theorem for a regenerative additive functional might imply a version of the center result, but one must actually check the coupling of cycle duration and displacement and its treatment of the unfinished cycle.

#### 2.2 Local Lamperti: retain, but describe its precise level

The existing statement is only

    N P(A_N=N/2) → (2/π)tan(πα/2),      0<α<1,

for the fresh pure-power law. This is not a uniform local limit over interior bins, not a boundary theorem, and not an equilibrium result. The macroscopic occupation law and continuum asymptotic densities are established prior art. The lattice pointwise upgrade is the potential contribution, subject to the remaining literature gap.

Strong renewal theorems are not interchangeable with this occupation theorem. In particular the familiar extra-hypothesis issues for the SRT at α≤1/2 do not automatically invalidate F's direct two-renewal argument, and absence of an SRT obstruction does not prove an all-L extension. F estimates the indexed sums themselves, rather than substituting a renewal-density asymptotic.

#### 2.3 Multidirection check: a bounded warning only

If one informally treats d occupation counts as a nondegenerate stable vector on a simplex of dimension d−1, the center would scale like a_N^(-(d−1)), while a stationary corner still has persistence order N^(1−α)L(N). The naive stable balance is

    1−α+(d−1)/α=0,
    α_d=[1+sqrt(4d−3)]/2.

For d=3 this already reaches α=2; for d>3 it leaves the stable range. The extrapolation therefore cannot support a multidirection theorem here. At and above that boundary the variance/norming regime changes. One also needs a specified direction chain, a nondegenerate spectral measure, correct lattice subperiods, and a model-specific corner event. “d directions” and spatial dimension d are different conventions. This warning is algebraic and conditional, not a literature-backed scaling assertion for an unspecified model. No multidirection computation was performed.

### Gaps

This pass used independent targeted web searches for WLH, persistent/renewal local limits, Lamperti pointwise results, Doney/DDS, Berger, and alternating-renewal occupation laws. It did not perform exhaustive MathSciNet/zbMATH searches, a complete forward-citation crawl, a full Russian-school semi-Markov LLT audit, or a page-by-page reading of all sources. Negative search results are evidence of non-location, not proof of originality. The published Engländer–Volkov book was not accessed.

## 3. Go/no-go verdict, priorities, and a realistic short-paper plan

### Takeaway

**Go for the focused heavy-tail paper, conditionally.** Replace the aging half with a properly proved general-tail local theorem and an accurate critical corollary. **No-go for presenting the unchanged pure-power balance plus a guessed logarithmic multiplier as a major new result.** A uniform finite-size window would strengthen the paper materially, but should enter the title or abstract only after its proof is complete.

### Cited Findings

- The existing main file combines two separate models and two proof appendices; the heavy-tail proof already has a self-contained two-renewal structure. This makes the proposed scope reduction technically natural. [Current main source](<C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/paperF/problem131_heavy_aging.tex>).
- The nearby literature already contains the heuristic balance, general stable functional scaling, and finite urn/count overlaps, as documented with exact primary locators in Section 2. The editorial verdict below is an inference from that overlap, not a claim about journal acceptance. [WLH](https://www.physik.uni-augsburg.de/theo1/hanggi/Papers/678.pdf), [Cénac et al.](https://arxiv.org/pdf/1612.00238v1), [DLS](https://arxiv.org/pdf/1901.08135v1).

### Inferences

#### 3.1 Recommended claim hierarchy

1. **Main theorem:** the finite-mean lattice center LLT for T∈RV(−α), 1<α<2, span 1, arbitrary independent a.s. finite first run. State the inverse norming explicitly. The tail-only proof above is preferable if an independent check confirms it.
2. **Main corollary:** exact stationary endpoint/center asymptotic with general L, and its fresh-start counterpart. Separate the universal index threshold from the nonuniversal critical slowly varying factor.
3. **Concrete critical example:** T(k)~A k^(-α)(log k)^β, including the corrected constant and the β>0/β<0 split at φ.
4. **Second theorem:** retain the present pure-law local Lamperti result. A regular-mass extension is a possible improvement, not a prerequisite for the first revised version.
5. **Optional strengthening:** prove uniformity in the exact pure-power α family, then give the κ_*=0.1833858634… window and an existence statement. Do not add uniqueness without a new argument.

A suitable working title would be “Local limits and endpoint balance for lattice Lévy walks.” A title about the golden ratio alone risks overstating a previously published heuristic.

#### 3.2 Concrete mathematical priorities

**Priority 0, before any manuscript rewrite:** independently verify the early-region argument using Caravenna–Doney Eq. (1.6). In particular check centering, the fixed interval selecting a lattice point, and the uniform Potter bound on m/a_m for m≤c h. This is the highest-value proof check because it removes a potentially artificial regular-mass hypothesis.

**Priority 1:** rewrite the abstract renewal proposition with a∈RV(1/α), and explicitly verify its first-passage/delay lemma under that assumption. Recompute the constants symbolically with the convention tT(a(t))→1. Use one positive-log and one negative-log example; specify valid small-k tails and their actual μ.

**Priority 2:** obtain one independent novelty check concentrated on regenerative/additive and semi-Markov lattice LLTs. The exact question is whether a published theorem already implies P(A_N=N/2)~2I_α/a(N/(2μ)) for this unfinished-cycle process and an arbitrary finite initial delay. Asking whether stable limits are known is too broad.

**Priority 3:** decide whether the moving-α proof fits in about two pages. The compact-parameter Fourier route is promising for the exact pure-power family, but general L and a varying family of body laws should be kept out of that first uniform theorem.

**Priority 4:** optional regular-mass local Lamperti extension. Do not let this or multidirection work delay the main paper. α≥2 can be a short comparison remark; α=1 can remain an explicitly open boundary case.

#### 3.3 Realistic page budget

| Component | Target pages |
|---|---:|
| Motivation, precise prior art, model and starts | 2 |
| Main general-tail LLT, ratio corollary, log example | 2–2.5 |
| Exact renewal identity and finite-mean proof | 3–4 |
| Local Lamperti statement and proof | 2.5–3.5 |
| Optional uniform pure-power α window | 1.5–2 |
| Limitations, brief Gaussian comparison, availability | 0.5–1 |
| References | 1.5–2 |

Aim for **12–15 pages including references without the uniform window**, or **14–17 with it**. These are editorial estimates, not compiled page counts. Keeping the full current α≥2 case split, long numerical tables, aging discussion, proof-verification inventory, and duplicated proof previews would defeat the shortening.

Move the substantial proof into the paper's main narrative rather than preserving a long statement section followed by a second exposition in an appendix. A compact appendix is reasonable only for a technical Fourier-uniformity lemma. One small illustration is enough; no new long sweeps are needed to motivate the theorem.

#### 3.4 Honest final novelty verdict

There is a viable short probability paper here if its center of gravity is the precise local theorem and its consequences for equilibrium persistence. The arbitrary-first-run feature, tail-only formulation, explicit inverse normalization, and sensitivity of the critical balance to slowly varying factors make a coherent package. The mathematics uses classical LLTs and local deviation estimates, so the novelty should be presented as a sharp theorem for this renewal walk and a clean proof, not a new stable-limit theory.

If a near-identical regenerative local theorem is found, the remaining balance/logarithm corollaries could be too routine for a substantial standalone contribution. In that event a brief note, or a paper with the completed uniform window and a broader interior LLT, is more realistic. Journal suitability cannot be settled from this initial search.

### Gaps

No revised manuscript, journal submission recommendation, acceptance prediction, numerical validation of an L-perturbed model, or completed uniform theorem is supplied. Those tasks require additional authorized work. This note's positive feasibility assessment rests on the explicit derivation in Section 1 and the bounded primary-source comparison in Section 2.
