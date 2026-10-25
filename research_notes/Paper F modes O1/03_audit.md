# Paper F, (O1): audit of the proposed results in 01_report.md and 02_report.md

Date: 2026-10-25. Read: `paperF/sec_setting.tex`, `sec_bigjump.tex` (Theorem B, Lemma
`lem:giant`, `lem:truncated`), `sec_shape.tex` (`thm:mode`, `thm:second-order`,
`lem:local-bigjump`, `lem:sums`, `thm:antimode`), `sec_preparation.tex` (statement of
Theorem C). Only the mathematics of the two reports is judged. Every proof step was
checked by hand. The only computation is the independent check in §8.

## Verdicts

| Result | Verdict |
|---|---|
| Lemma 1 (02 §1, self-contained proof) | proved as written (two harmless typos) |
| Lemma 2 (01 §3) | proved as written; the side remark on the case c = 1/μ_− overstates |
| Proposition 3 (fixed windows) | proved as written |
| Theorem 4 and its corollary (lower bound M_+ + M_− + 1) | proved as written, with endpoints counted as local maxima |
| (P0)–(P3), (P5) | proved as written |
| Theorem M1 | proved as written (one index typo, immaterial) |
| Theorem F2 (fallback) | (a)–(c) and the parity part of (d) proved; the last sentence of (d) is correct only after a restriction (§6) |
| Corrected criterion | correct as the statement to aim for; the plan's version is refuted by the fair zeta start; only the "only if" half is proved |
| Counterexample, four modes at N = 186 | confirmed in exact rational arithmetic, with endpoints counted |

## 1. Claim cards

**Lemma 1.** Hyp.: (RV), (SPAN) for the minus sign. Concl.: with t_n = T_−(n+1) and
d_n = u_−(n) − u_−(n−1) (u_−(−1) = 0), d ∈ ℓ¹ and d_n = −(1+o(1)) t_n/μ_−². So u_− is
eventually strictly decreasing, and so is every fresh-start end profile.

**Lemma 2.** Hyp.: (RV), (SPAN) for the minus sign; ν_−(d) = (c+o(1))T_−(d), c ≥ 0.
Concl.: for κ_+ of `eq:kappa-prep`, κ_+(j) − κ_+(j−1) = ((cμ_− − 1)/μ_−² + o(1)) T_−(j).

**Proposition 3.** Hyp.: (RV) plus; ν_+ = o(T_+); κ̃(0) = lim Q_+(N)/T_+(N) exists; no ties
on [0, J]. Concl.: for N ≥ N_0(J) and 0 ≤ j < J, P_N(N−j−1) − P_N(N−j) has the sign of
κ̃(j+1) − κ̃(j).

**Theorem 4.** Hyp.: (RV), (SPAN) both signs; bulk criterion; ν_± = o(T_±); κ̃_±(0) exist; no
ties up to beyond the last local maximum of κ̃_±. Concl.: for large N, P_N has at least
M_+ + M_− + 1 local maxima (an endpoint counts when it beats its one neighbour).

**Theorem M1.** Hyp.: (RV), (SPAN) minus; (LR) and (LR2-O) |f_+(n) − f_+(n+1)| = O(f_+(n)/n)
plus; fresh plus, fresh minus, or a mixture of the two. Concl.: uniformly in
1 ≤ j ≤ N^{1−η}, N(R_N(j+1) − R_N(j)) = NΔu(j) + Ψ(j) + o(1), with
Ψ = α_+[(j+1)Δu + 2μ_+Δv + 2u − 2μ_+w_−Δu], and Ψ = ΔC for the plus start.

**Theorem F2.** Hyp.: (RV), (SPAN), (LR), (LR2-O) both signs; fresh start or fair start; no
ties of κ̃_+ below J_+; η ∈ (0, 1 − 1/α_*), η' ∈ (0, x_*). Concl.: for large N, with
D_N(j) = P_N(N−j−1) − P_N(N−j): (a) sign D_N = sign Δκ̃_+ on j < J_+; (b) D_N < 0 on
[J_+, (x_*−η')Λ_N]; (c) D_N > 0 on [(x_*+η')Λ_N, N^{1−η}]; (d) an odd number of sign changes
in between, and the window contains Theorem E's j*_N. Mirror at the minus end.

## 2. The critical step of M1, derived independently

Theorem 5.1(b) gives R_N(j) = u(j) + C(j)/N + o(j/N). Differencing the main terms gives
ΔR_N = Δu + ΔC/N, but the error only differences to o(j/N), which is useless near
j ≍ Λ_N, where NΔu and ΔC are both O(1). So the difference must be taken inside the exact
identity. Write the fresh-plus identity as P_N(N−j) = Σ_m [a_m(j)Q_m(n) + V_m(n)b_m(j)]
with n = N−j, a_m = u^−_m, Q_m = q^+_{m+1}, V_m = f_+^{*m}, b_m = q^−_m. One difference in j
moves n to n−1, so four terms appear: Δa·Q, a·(n-difference of Q), V·Δb, (n-difference of
V)·b.

- In the first three, n-differences of Q_m are m-differences δV, and summation by parts in m
  turns Δa and Δb into m-differences of Q and V. Those are of order f_+(N), with limits f_+
  and 2μ_+f_+, because one extra run either covers the gap or adds μ_+ in mean. Only total
  variation bounds in m are needed on the minus side, and Lemma 1 (d ∈ ℓ¹) supplies them.
- The fourth term is the only genuine n-difference of a convolution power. Here
  f^{*m}(n−1) − f^{*m}(n) has no reason to be small under (LR) alone: a wiggle of f of
  relative size o(1) on a scale shorter than n changes it by o(f) but not by O(f/n), and the
  term is weighted by Σ_m b_m = 1, so it could be of order f_+(N), the same order as the main
  terms. With |f(n) − f(n+1)| ≤ Cf(n)/n, the giant-summand decomposition gives
  |f^{*m}(n−1) − f^{*m}(n)| ≤ Cmf(n)/n, and Σ_m m b_m(j) ≤ j+2 bounds the term by
  Cjf_+(N)/N = o(f_+(N)) for j ≤ N^{1−η}. So O(f/n) is exactly enough. It also predicts an
  error of size j/N in N·ΔR_N, which is what the reports' numerics show (about 30j/N).

This matches the written proof.

## 3. Lemma 1 (02 §1): line-by-line

- (1−z)T̂ = 1 − F, so D = 1/T̂: correct (t_0 = 1, t_n − t_{n−1} = −f(n)). Nonvanishing on the
  closed disk: a zero with |z| = 1, z ≠ 1 forces z^n = 1 on the support, which (SPAN)
  excludes. Wiener gives d ∈ ℓ¹.
- (W) and the product rule: correct. t is nonincreasing and positive, so c_t < ∞, and both
  halves of the split are dominated.
- Truncation: correct. One typo: 1/(1 − T̂''D) = Σ(+T̂''D)^k, so the series is
  d ∗ Σ(d∗t'')^{∗k}, not (−d∗t'')^{∗k}. The bound ‖e‖_1 ≤ 2‖d‖_1 is unaffected. T̂' is a
  polynomial without zeros in the closed disk, so e decays geometrically and e_n = o(t_n).
- Neumann series: c_t‖g‖_1 ≤ 1/4 gives x_k ≤ x_{k−1}/4 + C4^{−k}, hence x_k ≤ Ck4^{−k}.
  The induction (g^{∗k})_n/t_n → kĝ(1)^{k−1}χ_g and the sum −χ_g/(1+ĝ(1))² are correct
  (|ĝ(1)| ≤ 1/4).
- Constants: ê(1) = 1/T̂'(1), χ_g = ê(1), 1 + ĝ(1) = μ/T̂'(1), giving −1/μ². Correct.
- Consequences (a)–(c) of 01 §2 are correct. In (c), nonincreasing on j ≥ 1 plus eventually
  strictly decreasing to 1/μ_− gives u_− > 1/μ_− on j ≥ 1.

## 4. Lemma 2, Proposition 3, Theorem 4

- **Lemma 2.** For n ≥ 2, Δκ_+(n) = π_+d_n + (ν_−∗d)_n. This follows from the generating
  function π_+(U−1) + ν̂_−U. The product rule gives the limit −π_+/μ² − π_−/μ² + c/μ.
  Correct.
  - Overstatement in the case list: "c = 1/μ_− with π_− = 1 gives κ_+ ≡ 1/μ_−" holds only
    for ν_− = T_−/μ_− exactly (by `eq:cover`). With only ν_− ~ T_−/μ_−, Lemma 2 gives
    Δκ_+ = o(T_−) and says nothing more.
- **Proposition 3.** Immediate from Theorem B(a) for fresh starts (and for the fair start by
  linearity) and from Theorem C(d) when ν_+ = o(T_+). Correct.
- **Theorem 4.**
  - Each strict local maximum of κ̃ is copied by Proposition 3.
  - `thm:mode`(a) places every interior maximizer in pN + O(B_N). It is a local maximum, and
    it exceeds the end atoms, since T_±(N)B_N → 0.
  - The finiteness of M_± uses Lemma 2 with c = 0, because ν_∓ = o(T_∓) is assumed. This
    also makes M_∓ ≥ 1, which the corollary ("two maxima of one profile give at least four
    modes") needs.
  - Correct, with the convention that an endpoint is a local maximum when it beats its
    neighbour.
- **Fresh starts.** "M_+ = 1 iff u_− is nonincreasing on j ≥ 1" checks for all three starts:
  - plus start: κ̃(0) = 1;
  - minus start: κ̃(0) = 0;
  - fair start: κ̃(0) = 1/2, with the maximum at 0 or 1 depending on u(1).

## 5. M1 and (P0)–(P5): line-by-line

- **(P0).** Correct. It uses `lem:local-bigjump` at arguments ≥ n/2, with η slightly
  reduced, which is harmless.
- **(P3).**
  - No summand ≥ w: `lem:truncated` with z/(2w) → K_0/4 from below gives
    n^{−(α−1+η−ε)K_0/4}. The choice K_0 > 4(α+3)/(α−1) beats f(n)/n = n^{−α−2+o(1)} with
    margin.
  - First giant index I = i: the difference identity is exact. The first part is at most
    Cf(n)/n, by (LR2-O) at arguments ≥ n/K_0 and Σ_z h_i ≤ 1. The boundary term is at most
    Cmf(n)².
  - Summing over i ≤ m gives Cmf/n + Cm²f². The second is ≤ Cmf/n because mnf(n) ≍ mT(n) → 0.
  - The same w is used at n and n−1. Correct.
- **(P1).** Correct. The part x ≤ n/2 is Cμmf/n = o(f). For x > n/2:
  P(S_m ≥ n/2) ≤ CmT(n), P(S_m > εn) ≤ mμ/(εn), and f(n−y)/f(n) → 1 for y ≤ εn.
- **(P2).**
  - q_{m+2}(n) = Σ_x f(x)q_{m+1}(n−x) with q(k ≤ 0) = 0: correct, since S_{m+1} ≥ x ≥ n makes
    the event empty.
  - q_{m+1}(l−1) − q_{m+1}(l) = V_{m+1}(l−1) − V_m(l−1): verified by the set difference.
  - The x ≤ n/2 part is μf(n), by domination by Cxf(n). The x > n/2 part is μf(n), using
    Σ_y q_{m+1}(y) = μ and uniform tail control. Correct.
- **M1.** The four-term split is exact for j ≥ 1, n−1 ≥ 1. Minus-side facts:
  - 1, 3, 5, 6: verified.
  - 2: ΔĀ_i(j) = Σ_{x<j}u_i(x)d(j+1−x) + u_i(j)u(1), so Σ_i|ΔĀ_i| ≤ ‖Δu‖_1 + 1 exactly as
    stated.
  - 4: (v+u) = u∗u, so Δ(v+u)(j) = [z^{j+1}]U·D, not [z^j]. The bound |Δv| ≤ 1 + ‖d‖_1 is
    unchanged.
- **The terms.**
  - II and III: by (P1), each is f_+(N)u(j) + o(f_+(N)). In III, the minus start's
    f_−(j) − u^−_1(j) cancels exactly.
  - IV: ≤ Cf_+(N)(j+3)/N.
  - I: Q_1(n−1)Δu + Σ_iδ_iΔĀ_i, where δ_i = 2μ_+f_+(N)(1+o(1)) uniformly by (P2), and fact 2
    absorbs the o(1). The o((j+1)f)·Δu error is o(f) by fact 3.
- **The sum.** The bracket reproduces Ψ for both starts and ΔC for the plus start
  (ΔC = α_+[(j+1)Δu + 2μ_+Δv + 2u(j)], checked from `eq:Cj`). Linearity covers mixtures.
- **Uniformity.** Every m that occurs satisfies m ≤ j+2 ≤ N^{1−η}+2, which is within the
  (P)-range at arguments ≥ N/2 after replacing η by η/2. The (P) lemmas use only
  `lem:local-bigjump`, `lem:truncated`, `lem:sums` and `lem:rv` in their stated ranges.
- **Remark Ψ → c_a.** Correct: Δ(v+u) → d̂(1)/μ_− = 1/μ_−², and Δu → 0.

**Verdict: proved as written.**

## 6. Theorem F2 and the zones

- **Zones.** [0, J_+) is covered by Proposition 3. [J_+, J') is covered by Proposition 3,
  using strict decrease of u. [J', (x_*−η')Λ_N] is covered by M1 and Lemma 1, with J' chosen
  after η' and N after J'. ((x_*−η')Λ_N, (x_*+η')Λ_N) is covered by parity only.
  [(x_*+η')Λ_N, N^{1−η}] is covered by M1.
- **Junctions.** Consecutive integer intervals abut, so there is no gap. (b) and (c) need
  (x_*+η')Λ_N ≤ N^{1−η}, which η < 1 − 1/α_* gives at both ends.
- **(b).**
  - The relative error of Lemma 1 multiplies NT_−(j)/μ_−², which dominates, so it is harmless.
  - NT_−((x_*−η')Λ_N) → (x_*−η')^{−α_−} > c_aμ_−², and sup_{j≥J'}Ψ ≤ c_a + o_{J'}(1).
  - Correct.
- **(c).** Symmetric. It uses inf_{j≥(x_*+η')Λ_N}Ψ → c_a. Correct.
- **Parity.** D_N < 0 at the left end of the window and > 0 at the right end. So the number
  of strict sign changes, after deleting zeros of D_N, is odd. The extrema alternate min,
  max, …, min, with one more minimum than maximum. Correct. If D_N vanishes somewhere, a tie
  makes a plateau, and "number of extrema" must count plateaus once. The no-ties hypothesis
  does not cover the window.
- **Restriction needed in (d).** "The window contains Theorem E's j*_N" holds only for a
  fresh plus start with u_−(j) > 1/μ_− for all j ≥ 1, where Theorem E(a) gives
  j*_N/Λ_N → x_*.
  - Minus start: P_N(N) = 0 is the global minimum.
  - Fresh plus start with inf_{j≥1}u_− < 1/μ_− (for example runs ≥ 2): Theorem E(b) makes
    j*_N bounded.
  - Fair start: Theorem E is not proved for it.
  - In every case the window contains the minimizer of P_N(N−j) over
    J_+ ≤ j ≤ N^{1−η}, by (b) and (c).
- **Width.** "Width o(Λ_N)" follows from (b)–(c) for every η' by a diagonal choice
  η'_N → 0. Correct.

**Verdict: correct after the restriction of the last clause of (d) stated above.**

## 7. The criterion

- **The plan's criterion is false.** "Three modes iff both κ_± monotone" fails for the
  fair zeta start.
  - The profile κ̃_+ = (1/2, f(1), u(2), …) has f(1) = 1/ζ(5/2) = 0.7454 > 1/2, so it is not
    monotone.
  - My own float recursion (§8) gives exactly three local maxima: k = 1, 200, 399 at
    N = 400, and k = 1, 1000, 1999 at N = 2000.
  - The sign changes at N = 2000 are 1, 16, 1000, 1984, 1999, as in the plan.
- **The corrected criterion fits the data.** "Each κ̃_± has exactly one local maximum"
  matches: the unique maximum at j = 1 is copied to N−1, and the endpoint N is then not a
  maximum.
- **What is proved.** For fresh and fair starts, M_± ≥ 1 always (Lemma 1), so the criterion
  is the same as "M_+ + M_− + 1 ≤ 3". Its "only if" half is Theorem 4. The "if" half still
  needs M2–M4.

## 8. Independent check of the counterexample

- **Parameters.** These were taken from `inspect_cm.py` / `check_cm_everyN.py`. The same law
  is used for both signs, P(X = n) = Σ_c w_c(1−θ_c)θ_c^{n−1}, with a fresh plus start.
  - Case 1: w = (9/10, 1/10), θ = (1/10, 99/100), N = 186.
  - Case 2: w = (1/2, 1/2), θ = (3/10, 97/100), N = 131.
- **Method.** A geometric mixture is a hidden Markov chain on (plus count, sign, component).
  A run continues with probability θ_c. Otherwise it switches sign and draws a new component
  from w. I ran this recursion in exact rational arithmetic.
  - Checks: Σ_k P_N(k) = 1 exactly, and P_N(N) = T(N) exactly.
  - It agrees with brute-force enumeration of run compositions at N = 1, 2, 5, 9.
  - Scripts: `py -I cm_exact.py` and `py -I brute_check.py`, in the scratch folder
    `audit/`.
- **Results.** There are no ties. The strict local maxima are:
  - N = 186: k = 3, 97, 184, 186. The sign changes of ΔP are at 3, 48, 97, 137, 184, 185.
  - N = 131: k = 4, 71, 129, 131.
- **Size of the gaps.** The smallest relative gap at a maximum is 1.6·10⁻⁵ (k = 97). So
  02's sentence "relative differences at least 5·10⁻⁵" is inaccurate, but the exact
  arithmetic settles the sign.
- **Scope.**
  - The four modes include the endpoint atom k = N. Counting interior local maxima only,
    both cases have three.
  - The paper's asymptotic three-mode picture for a fresh plus start includes k = N, so the
    endpoint convention is the consistent one, and under it "at most three local maxima for
    every N for completely monotone laws" is refuted.
  - The law has exponential tails, so (RV) fails. The example says nothing about laws under
    the paper's hypotheses.
  - The geometric mixture is strictly log-convex, so u is strictly decreasing and κ̃_+ has a
    single maximum. The extra maximum at N−2 is a finite-N effect, not a copy of κ̃_+.

## 9. Corrections to carry into any write-up

1. Lemma 1, truncation step: the sign in the series for e.
2. M1, fact 4: the index [z^{j+1}].
3. Lemma 2: the c = 1/μ_− case needs ν_− = T_−/μ_− exactly.
4. F2(d): restrict the clause on j*_N to the fresh plus start with u_− > 1/μ_− on j ≥ 1.
   Otherwise replace it by the minimizer over [J_+, N^{1−η}].
5. State the endpoint convention for "local maximum" wherever modes are counted, including
   the counterexample.
6. The counterexample: replace "at least 5·10⁻⁵" by the exact statement.
