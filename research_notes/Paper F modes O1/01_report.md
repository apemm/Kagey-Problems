# Paper F, (O1): the modal structure of P_N

Date: 2026-10-25. Manuscript read: `kagey-problems/problem131/paperF`
(problem131_levy.tex and its sections, working tree). Plan read: `01_F_plan_EJP.md` §2 and
`04_F_modes_numerics.md`. I did not run the plan's scripts. Every number below comes
from the scripts in this folder, run with `py -I`.

## 0. Summary

1. **The target is right, with one correction.** My own exact recursion reproduces every
   number in the plan except one antimode position, which is off by one (§1). In every law
   tested, the layer extrema of P_N sit exactly at those of κ. They are followed by exactly
   one antimode, and then one bulk mode.
   - **The correction.** The criterion "exactly three local maxima iff both κ_± are monotone"
     is false as stated. With a fair start and the zeta law (α = 3/2), the plus-end profile is
     κ̃ = (1/2, u(1), u(2), …) with u(1) = f(1) = 0.745 > 1/2. So κ̃ is not monotone, yet the
     law has exactly three modes.
   - **The correct criterion.** Each end profile κ̃_± (with κ̃(0) = lim P_N(N)/T_+(N)) has
     exactly one local maximum. For fresh starts this is the same as u_∓ being nonincreasing
     on j ≥ 1.
2. **Proved here, rigorous modulo one cited classical theorem.**
   - **Lemma 1.** Under (RV)+(SPAN), u(j) − u(j−1) ~ −T(j)/μ². So κ is eventually strictly
     monotone for every fresh start, with no extra hypothesis. The plan's hypothesis
     "κ has finitely many extrema" is automatic.
   - **Lemma 2.** The same asymptotics for the prepared kernel of Theorem C:
     Δκ ~ (cμ_− − 1)T_−/μ_−².
3. **Proved here.**
   - **Proposition 3.** Copying of the κ-extrema on fixed windows.
   - **Theorem 4.** For all large N, P_N has at least M_+ + M_− + 1 local maxima. So the
     "only if" half of the criterion holds: a non-unimodal profile forces at least four modes.
     Examples include the zeta law on runs ≥ 2 (at least 15 local maxima) and a log-convex law
     with a prepared start (§5).
4. **Not proved.** The "if" half: exactly one antimode, and monotonicity from it to the bulk.
   F proves no estimate at the level of differences. The first missing implication is
   Lemma M1 (§6), a first-difference version of Theorem 5.1(b) with error o(1/N).
   - My heuristic analysis and one numerical case suggest that (LR) is not enough for M1.
     A second-order local hypothesis such as (LR2), f(n) − f(n+1) ~ (α+1)f(n)/n, looks
     necessary.
   - Log-convexity together with (LR) implies (LR2) (Lemma 5).
5. **The link to Theorem C: yes, the preparation changes the number of modes.** Take the
   log-convex zeta law with a minus initial run of law ∝ T_−(d) on d ≥ 2. Then κ_+ increases
   to 1/μ from below, the antimode disappears, and the exact law has only **two** local maxima
   at every N tested (§5, P7).

## 1. Numerics: reproduction of the plan (predictions in `00_predictions.md`)

The engine is `engine.py`, an exact 2D renewal recursion in (plus steps, minus steps) with
nonnegative sums in float64. `check_engine.py` checks it against a brute-force Markov DP over
(count, sign, age): the maximum difference is 4e-16 at N = 5, 17, 40.

| Check | Command | Plan | Mine |
|---|---|---|---|
| fair, α=1.5/1.5, N=2000 | `py -I repro_plan.py single` | k=1,16,1000,1984,1999 | identical |
| fair, α=1.9/1.3, N=2000 | same | 1,8,773,1976,1999 | identical |
| scan N≤400, first N with 5 changes | `py -I repro_plan.py scan` | 60, 98, 152, 162, 162 | identical; counts ⊂ {1,3,5}, never above 5 |
| runs ≥ 2, fair, total changes at N=100,200,500,1000 | `py -I repro_plan.py nonlc` | 15,19,23,31 | identical |
| same, per side at N=1500..4000 | same | 17,15,13,13 | identical |
| layer match, fresh plus, N=3000 | `py -I repro_plan.py layer` | zeta: j=22; f(2)×2: 1,2,20; f(2)×4: 1..4,17; runs≥2: 1..12,28 | identical, except f(2)×4 gives antimode 18 (not 17), probably a normalization difference |

Predictions P1–P3 hold.

**New checks.**

- **P4** (`py -I check_du.py`, confirmed). The ratio (u(j)−u(j−1))μ²/T(j) at j = 10, 10², 10³,
  5·10³, 2·10⁴:
  - α=1.5: −0.963, −0.996, −0.9996, −0.9999, −1.0000;
  - α=1.8: −0.759, …, −0.9987;
  - α=1.2: −2.42, …, −1.21 (slow, rate about j^{1−α});
  - runs ≥ 2: the last increase of u is at j = 12, and the ratio is −1.0000 at 2·10⁴.
- **P5** (`py -I check_diff_layer.py`, confirmed). For the zeta law (α=1.5, fresh plus), compare
  N(R_N(j+1)−R_N(j)) with NΔu(j)+ΔC(j):
  - The discrepancy is about 34·j/N at every N tested (for example 0.73, 0.227 and 0.066 at
    j = 20 for N = 10³, 3·10³ and 10⁴). That is an O(j/N) correction, which tends to zero on
    j = O(N^{1/α}).
  - The local minimum of R_N is at j = 10, 22, 51, against 10, 23, 53 for u+C/N.
  - The second differences of R_N are strictly positive on [1, 3j*) at all three N, so R_N is
    convex across the layer and past the antimode.
- **P6, P7** (`py -I check_prepared.py`, both confirmed): see §5.
- **P8** (`check_wiggle.py`, `check_wiggle_layer.py`): only partly confirmed. Take
  f_+ ∝ n^{−5/2}(1+ε sin(2πn/w)).
  - With ε=0.3, w=60 and N=3000, the antimode splits into three extrema (j = 17, 24, 31).
  - With ε=0.3, w=60, at N = 1500, 6000 and 10000, and in every other case tried, the
    structure is unchanged. Fixed-scale wiggles are smoothed out as N grows, as the
    heuristic in §6 predicts.
  - The big-jump zone stayed monotone in every case tried.
  - So P8 is **not** established as an asymptotic counterexample. It shows only that a
    wiggle at the right scale relative to N can split the antimode.

## 2. Lemma 1 (difference renewal theorem), rigorous modulo a cited theorem

**Lemma 1.** Assume (RV) and (SPAN) for the minus sign, and write u = u_−, T = T_−, μ = μ_−.
Then u(j) − u(j−1) = −(1+o(1)) T(j)/μ² as j → ∞.

*Proof.*
- Put t_n = T(n+1) (n ≥ 0) and T̂(z) = Σ t_n zⁿ. Then (1−z)T̂(z) = 1 − F(z), so
  (1−z)U(z) = 1/T̂(z). Hence d_n := u(n) − u(n−1) (with u(−1) = 0) are the coefficients of
  1/T̂.
- On |z| ≤ 1, T̂(z) = 0 forces F(z) = 1 with z ≠ 1, which (SPAN) excludes; and T̂(1) = μ.
  So 1/T̂ is analytic on a neighbourhood of the compact set T̂(closed disk).
- The sequence t is regularly varying with index −α < −1. So it is summable, t_{n+1}/t_n → 1,
  and (t∗t)_n ~ 2μ t_n: split the convolution at n/2 and use dominated convergence with
  Lemma `lem:rv`(i),(ii).
- The sequence form of the theorem of Chover, Ney and Wainger (J. Analyse Math. 26 (1973);
  discrete form in Embrechts–Omey, Yokohama Math. J. 32 (1984)) says that if φ is analytic
  near the range of â on the closed disk, then [zⁿ]φ(â) ~ φ'(Σa) a_n. With φ(w) = 1/w this
  gives d_n ~ −t_n/μ² ~ −T(n)/μ². ∎
- *Caveat:* I did not check the theorem numbers against the sources in this session.
  `mathbox:literature-check` should confirm them before the result is used in F.

**Consequences.**
- (a) u_− is eventually strictly decreasing, so it has only finitely many local extrema, under
  (RV)+(SPAN) alone. For every fresh start, κ^{(σ0)}_+ (eq. `eq:kappa`) differs from u_− only
  at j = 0, so the plan's hypothesis "κ has finitely many extrema" is automatic. The plan's
  suggested route through "eventually monotone f under (LR)" is not needed.
- (b) Summing Lemma 1 over j' > j and applying Karamata gives back F's
  `eq:second-renewal` (Frenk), so Lemma 1 is the local form of it.
- (c) If u_− is nonincreasing, then u_−(j) > 1/μ_− for all j ≥ 1, since u_− is eventually
  strictly decreasing. So Theorem E(a) applies to every law with monotone u_−. The borderline
  case excluded after Theorem E (u ≥ 1/μ with equality somewhere) always has non-monotone u.
  This could be a one-line remark in F.

## 3. Lemma 2 (prepared kernel)

Take κ_+ of `eq:kappa-prep`: for j ≥ 1, κ_+(j) = π_+u(j) + Σ_{d=1}^{j} ν_−(d)u(j−d).

**Lemma 2.** Assume (RV),(SPAN) for the minus sign, and ν_−(d) = (c+o(1))T_−(d) with c ≥ 0
(c = 0 means ν_− = o(T_−)). Then κ_+(j) − κ_+(j−1) = ((cμ_− − 1)/μ_−² + o(1)) T_−(j).

*Proof.*
- For n ≥ 2, Δκ_+(n) = [zⁿ] (π_+ + ν̂_−(z))/T̂(z) = π_+d_n + (ν_−∗d)_n.
- Elementary convolution lemma: if a_n ~ c_a t_n and b_n ~ c_b t_n, both summable, then
  (a∗b)_n ~ (c_a B(1) + c_b A(1)) t_n. Split at n/2. Since |b_m| ≤ Ct_m, the ratios
  t_{n−k}/t_n are bounded for k ≤ n/2 and tend to 1 for k ≤ εn, and dominated convergence
  applies.
- Apply it with a = ν_−, A(1) = π_−, b = d, B(1) = 1/μ_− and c_b = −1/μ_−², then add
  π_+d_n. ∎

**Cases.**
- **c < 1/μ_−: κ_+ is eventually decreasing.** This covers fresh starts, ν_− = o(T_−), and the
  stationary initial run (c = 1/s). For the stationary run, Theorem C(d) with (Rν) gives the
  profile 2(μ_+u_−(j)+1)/s on j ≥ 1, which is monotone like u_−.
- **c > 1/μ_−: κ_+ is eventually increasing, to 1/μ_− from below.** Example:
  ν_−(d) = T_−(d)/(μ_−−1) for d ≥ 2, so c = 1/(μ_−−1).
- **c = 1/μ_− with π_− = 1: κ_+ ≡ 1/μ_− on j ≥ 1.** This is the equilibrium delayed renewal
  process. The layer is flat at first order and its shape is set at second order. This case
  is degenerate, and I did not study it.

## 4. Fixed windows and the lower bound (proved)

Hypothesis (NT_J): κ̃(j+1) ≠ κ̃(j) for 0 ≤ j < J. Here κ̃(0) = lim Q_+(N)/T_+(N) (assumed to
exist) and κ̃(j) = κ_+(j) for j ≥ 1. The same hypothesis applies at the minus end.

**Proposition 3.** Assume (RV) for the plus sign, an initial run with ν_+(n) = o(T_+(n)), and
(NT_J). Then for N ≥ N_0(J) and 0 ≤ j < J, P_N(N−j−1) − P_N(N−j) has the sign of
κ̃(j+1) − κ̃(j).

*Proof.* Theorem `thm:preparation`(d), or `thm:bigjump`(a) for fresh starts, gives
P_N(N−j)/T_+(N) → κ̃(j) for each of the finitely many j ≤ J, and the gaps
|κ̃(j+1)−κ̃(j)| > 0. ∎

Let M_+ be the number of strict local maxima of κ̃_+ on {0,1,…}, where j = 0 counts if
κ̃(0) > κ̃(1). M_+ is finite whenever κ̃_+ is eventually strictly monotone, for instance in
every case of Lemma 2 with c ≠ 1/μ_−.

**Theorem 4.** Assume (RV),(SPAN) for both signs, the bulk criterion, ν_±(n) = o(T_±(n)),
existence of the limits κ̃_±(0), and (NT) on [0, J_±+1], where J_± lies beyond the last local
maximum of κ̃_±. Then for all large N, P_N has at least M_+ + M_− + 1 local maxima.

*Proof.*
- By Proposition 3, each strict local maximum j0 of κ̃_+ is a local maximum of P_N at N−j0,
  and similarly at the minus end.
- By `thm:mode`(a), the interior maximizer of P_N lies in pN+O(B_N), so it is a local maximum
  distinct from all of these.
- These points are distinct once N > 2max(J_±) + O(B_N). ∎

**Corollary (the "only if" half).** Under these hypotheses, if some κ̃_± has two or more local
maxima, then P_N eventually has at least four local maxima.

- **Fresh starts.** At the plus end κ̃_+ is u_− (plus start), (0, u_−(1), …) (minus start) or
  (1/2, u_−(1), …) (fair start). In each case M_+ = 1 if and only if u_− is nonincreasing on
  j ≥ 1. This follows from Lemma 1, since u_− is eventually strictly decreasing.
- **Log-convex laws** have M_± = 1 by `lem:logconvex`.
- **Zeta law on runs ≥ 2** (α = 3/2, fair start). Here u(0..15) = 1, 0, .5177, .1879, .3595,
  .2469, .3020, .2622, .2788, .2639, .2680, .2617, .2619, .2587, .2579, .2559. Its local maxima
  are at j = 0, 2, 4, …, 12, so M_± = 7 and P_N eventually has **at least 15** local maxima.
  - This uses the decreasing tail from Lemma 1 and the double-precision values above, whose
    smallest gap is 2·10⁻⁴. The gaps are not interval-certified.
  - The count agrees with the 27 sign changes found at N = 3000 and 4000.

## 5. The link to Theorem C: preparation changes the number of modes (log-convex law)

All rows use the zeta law with α = 3/2 for both signs; command `py -I check_prepared.py`.

**P6.** Initial run: fresh plus with probability 1/2, or a minus run of length exactly 5 with
probability 1/2. Then
κ̃_+ = (0.5, .3727, .3437, .3293, .3202, .8139, .6818, …), with a local minimum at j = 4 and a
local maximum at j = 5. Theorem 4 applies: ν_+ = f_+/2 = o(T_+). The exact law has local
maxima at k = 1, N/2−1, N−5 and N for N = 200, 1000 and 3000. That is four modes, against
three for the fresh law. The R_N(0..8) values converge to κ̃.

**P7.** Initial run: minus, with ν_−(d) = T_−(d)/(μ−1) on d ≥ 2.
- Lemma 2 predicts c·μ − 1 = 1.0556. The exact Δκ·μ²/T at j = 300 is 1.0595, and κ_+ is
  strictly increasing on [2, 400) to 1/μ = 0.5135.
- The exact law has exactly **two** local maxima, the atom at k = 0 and the bulk mode, for
  N = 500, 1000, 2000 and 3000. There is no sign change of ΔP_N on k > N/2: the plus side is
  monotone from the bulk to the end, with no antimode.

**What is proved and what is not.**
- P6 is proved for all large N by Theorem 4 together with Theorem C(d), as a lower bound
  (at least four modes).
- P7 (exactly two modes, no antimode) is numerical only. Proving it needs the analogue of
  M1–M3 for the prepared kernel.
- This sharpens the answer to the Wang–Schulz–Deng–Barkai question: the preparation can
  change the shape of the law, including the number of modes, even for a completely monotone
  run law.

## 6. The full structure: proof up to named lemmas

Fix a fresh plus start, (RV),(SPAN) for both signs, (LR) for the plus sign, and
b_{+,N} ≍ B_N (for example equal indices). The last condition avoids the window that F does
not describe. Write R_N(j) = P_N(N−j)/T_+(N), D_N(j) = R_N(j+1) − R_N(j), Λ_N = a_−(N),
c_a = 2α_+s/μ_−², and x_* with x_*^{−α_−} = 2α_+s, as in `thm:antimode`.

### The missing lemmas

None of these is in F. F's estimates are all at the level of values, with relative errors
o(1) or o(j/N).

- **(M1) First differences, second order.** For every K, uniformly in 0 ≤ j ≤ KΛ_N:
  N D_N(j) = N Δu(j) + ΔC(j) + o(1).
  - This is the difference form of `thm:second-order`(b) with the error improved from o(j/N)
    to o(1/N).
  - Numerically the error is about 34j/N (P5).
  - A weaker form, |N D_N(j) − NΔu(j)| ≤ C for j ≤ εΛ_N, already gives zone 2 below.
- **(M2) Convexity at the antimode.** There are η, c > 0 with
  NΛ_N(R_N(j+2) − 2R_N(j+1) + R_N(j)) ≥ c for |j − x_*Λ_N| ≤ ηΛ_N.
  - Numerically the second differences are positive on all of [1, 3j*).
- **(M3) Monotone big-jump zone.** For every K large, P_N(k−1) > P_N(k) for
  pN + KB_N ≤ k ≤ N − KΛ_N and all large N.
  - This is a difference form of `thm:bigjump`(b) together with the junction with M1 at
    j ≍ Λ_N.
- **(M4) Bulk.** On |k − pN| ≤ KB_N, ΔP_N changes sign exactly once, and the junction with M3
  holds.
  - It would follow from a derivative local limit theorem, B_N²ΔP_N(k) = h_N'(x_{N,k}) + o(1)
    uniformly, together with a second-derivative version near the mode, and the bell shape of
    stable densities (Kwaśnicki; Kwaśnicki–Simon; the citation is to be checked).
  - Bell shape gives a single zero of h' with h'' < 0 there. When the indices differ, only the
    limit θ ∈ {(1,0),(0,1)} matters.

### Deduction (rigorous, given M1–M4)

Zones are listed in order of increasing j.

- **Zone 1, j < J.** Proposition 3 copies the extrema of u. Choose J beyond the last change of
  sign of Δu, which exists by Lemma 1.
- **Zone 2, J ≤ j ≤ εΛ_N.**
  - ΔC(j) → c_a. Indeed ΔC = α_+[u(j+1) + u(j) + jΔu(j) + 2μ_+Δv(j)], jΔu(j) → 0 by Lemma 1,
    and Δ(v+u)(j) = [z^j]U·(1/T̂) → 1/μ_−² by dominated convergence.
  - By Lemma 1, NΔu(j) ≤ −NT_−(εΛ_N)/(2μ_−²) → −ε^{−α_−}/(2μ_−²).
  - With M1 (even its weak form), D_N < 0 for ε small.
- **Zone 3, εΛ_N ≤ j ≤ KΛ_N.**
  - M1, Lemma 1 and (RV) give N D_N(j) = Φ(j/Λ_N) + o(1), with
    Φ(x) = c_a − x^{−α_−}/μ_−². Φ is strictly increasing and vanishes exactly at x_*.
  - So D_N < 0 on [εΛ_N, (x_*−η)Λ_N] and D_N > 0 on [(x_*+η)Λ_N, KΛ_N].
  - M2 makes D_N strictly increasing on the η-window, so it changes sign there exactly once.
  - That single change is a local minimum and the minimum over the zone. So by Steps 2–4 of
    `thm:antimode`'s proof it is Theorem E's j*_N.
- **Zone 4, from the antimode to the bulk.** M3, then M4: one sign change, the bulk mode.
- **The mirror** at the minus end.

**Conclusion (conditional).** For all large N, the local extrema of P_N are:
1. those of κ̃_± at the same positions;
2. exactly one antimode at each end, at N − j*_N and its mirror;
3. exactly one bulk mode.

So the number of local maxima is M_+ + M_− + 1, and it equals 3 if and only if M_± = 1.

### The first missing implication: M1, and why (LR) is probably not enough

Differencing the final-run identity `eq:final-explicit` in j splits D_N T_+(N) into two parts.

**A-part** (final plus run).
- It equals T_+(N)Δu(j) + Σ_x ρ_j(x) f_+(N−j−1−x) + Σ_x Δρ_j(x)[T_+(N−j−1−x) − T_+(N)].
- The terms are smooth in j once one shows Σ_r |A_r(j)| = O(1) uniformly, where
  A_r(j) = Σ_{r'≤r}(u^−_{r'}(j+1) − u^−_{r'}(j)). This is a difference local limit theorem for
  the index of the covering run, which F's Lemma `lem:index` gives only at the value level.
- It also needs f^{*(r+1)}(n) − f^{*r}(n) = f(n)(1+o(1)) uniformly for r ≤ n^{1−η}.

**B-part** (a complete giant plus run, then a final minus run of length m ≤ j).
- It contains Σ_m T_−(m) Σ_r u^−_r(j−m)[f^{*(r+1)}(N−j−1) − f^{*(r+1)}(N−j)].
- `lem:local-bigjump` bounds this only by o(j f_+(N)) = o(jT_+(N)/N). Near j ≍ Λ_N that is not
  o(T_+(N)/N).
- Here f_+ is read at N−j, smoothed only over S^+_r with r ≲ j, that is on the scale
  a_+(Λ_N) ≪ Λ_N.

**What suffices.** Splitting by the first summand above n/(2m_0), together with the truncated
deviation bound `lem:truncated` for the event with no such summand, gives
|f^{*r}(n−1) − f^{*r}(n)| ≤ C r f(n)/n for r ≤ n^{1−η}. That makes the B-part error
O(jT_+/N²) = o(T_+/N). The bound needs:

> **(LR2)** f_+(n) − f_+(n+1) ~ (α_++1) f_+(n)/n
> (an O-version suffices for the B-part, the asymptotic version for the A-part).

**Heuristic that (LR) is not enough.**
- Take f_+(n) = c n^{−α−1}(1 + ε_n sin(n^θ)) with ε_n = 1/log n. This satisfies (LR), and has
  local wiggle period w(n) ≍ n^{1−θ}.
- Choose a_+(Λ_N) ≪ w(N) ≪ ε_NΛ_N. This is possible because a_+(Λ_N) ≪ Λ_N.
- The wiggle in N·D_N near j*_N then has size about ε_NΛ_N/w(N) → ∞. That swamps the slope
  about 1/Λ_N per step that M2 needs, and would split the antimode.
- P8 shows this mechanism at one resonant N (three extrema at N = 3000) but not as N → ∞.
- So this is a conjecture, not a proved counterexample.

**Lemma 5 (proved).** If f is positive, log-convex and satisfies (LR), then it satisfies
(LR2).

*Proof.*
- δ_n = 1 − f(n+1)/f(n) is nonincreasing and positive, since otherwise f would not tend to 0.
- (LR) gives f ∈ RV_{−α−1}, so Σ_{n≤i<λn} −log(1−δ_i) → (α+1)log λ for every λ > 1, and
  δ_i → 0.
- Monotonicity bounds the sum between (λ−1)nδ_{⌈λn⌉}(1+o(1)) and (λ−1)nδ_n(1+o(1)).
- Letting λ ↓ 1, and repeating on [λn, n) for λ < 1, gives nδ_n → α+1. ∎

So the corrected target hypothesis is natural: (RV),(SPAN), and (LR2) for both signs (or
log-convex laws with (LR)).

## 7. Labels of F used

`eq:kappa`, `eq:cover`, `eq:conv-v`, `eq:final-explicit`, `eq:rho-rep`, `eq:kappa-prep`,
`thm:bigjump`(a),(b), `thm:preparation`(d), `thm:mode`(a), `thm:second-order` (with C(j) of
`eq:Cj`), `thm:antimode` (Steps 2–4), `eq:second-renewal`, `lem:logconvex`, `lem:local-bigjump`,
`lem:truncated`, `lem:index`, `lem:rv`, `thm:bulk`(c), `lem:profile`(d). F's sentence "the
number of local extrema inside the layers is not determined here" stays true after this
work, except for the lower bound (Theorem 4).

## 8. Honest status

| Claim | Status |
|---|---|
| Lemma 1, Lemma 2 | proved, modulo the citation of Chover–Ney–Wainger (theorem number to be checked) |
| Proposition 3, Theorem 4, the "only if" half, Lemma 5, the zeta-on-runs-≥2 bound of at least 15 modes, the P6 example (at least 4 modes) | proved |
| Exactly one antimode, monotonicity to the bulk, exactly three modes for log-convex laws, P7 (exactly two modes) | open; reduced to M1–M4. M1 is the first missing step and probably needs (LR2) |
| (LR) is insufficient | heuristic plus one numerical case, not proved |

The every-N stretch goal (at most three modes for completely monotone laws) was not
attempted beyond reproducing the N ≤ 400 scan.

## Files

- `00_predictions.md`: predictions written before the runs.
- `engine.py`: the exact recursion; `check_engine.py`: the brute-force check.
- `repro_plan.py` (`single`, `scan`, `nonlc`, `layer`), `check_du.py`, `check_diff_layer.py`,
  `check_prepared.py`, `check_wiggle.py`, `check_wiggle_layer.py`.
- Run times: each takes under 30 s except `repro_plan.py nonlc layer` (about 30 s together).
