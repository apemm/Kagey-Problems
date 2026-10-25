# Paper F, (O1), fourth round: the upper bound, and the exact eventual mode count

Date: 2026-10-25. Read: `paperF/sec_setting.tex`, `sec_bulk.tex` (Theorem A = `thm:bulk`),
`sec_appendix.tex` (`lem:stable`, `lem:kernels`, `lem:small`), `sec_bigjump.tex`
(Theorem B, `lem:truncated`), `sec_shape.tex` (§5.4: `lem:diff-renewal`, `lem:plus-diff`,
`thm:first-diff`, `thm:ends`, `thm:modes-lower`, `conj:three-modes`), the notes 01, 02, 03,
and item 1 of the plan `F_plan.md` (read only; none of its scripts was run). The paper was
not edited. The predictions are in `04_predictions.md` and were written before any run.

## 0. Summary

1. **The conjecture is proved for comparable scales** (Theorem 1, §1). Assume (SPAN), (LR) and
   a second-difference bound (LD2) for both signs, and (EQ): T_+(n)/T_−(n) stays bounded away
   from 0 and ∞, which forces α_+ = α_−. Take a fresh start of either sign or the fair start,
   with the no-tie condition of `thm:ends`. Then for all large N, P_N has exactly
   M_+ + M_− + 1 modes. The theorem gives the whole sign pattern of ΔP_N.
   - (LD2) is f(n+1) − 2f(n) + f(n−1) = O(f(n)/n²). It implies the paper's (LD) and the
     asymptotic form f(n) − f(n+1) ~ (α+1)f(n)/n (Lemma 2).
2. **The three steps.**
   - **(b) One antimode.** Proved under (LR), (LD2), with no condition on the scales. j ↦ P_N(N−j)
     is strictly convex from a fixed J_0 to every fixed multiple of Λ_N = a_−(N) (Theorem 7).
   - **(c) Big-jump zone.** Proved. The main new lemma is a difference form of the local big-jump
     theorem for sums of m runs, uniform in m up to order N (Lemma 8). From it, D_N = (1+o(1))∂_jG_N
     on the whole zone (Theorem 10). (EQ) is used here only to control indices with a left
     deviation of the minus sum near L ≍ B_N. Without (EQ) the zone is covered from Kλ_NB_N on.
   - **(a) Bulk.** Proved under (EQ). The kernel differences come from Gnedenko's Fourier proof
     (Lemma 11), the bell shape comes from Kwaśnicki, and analyticity gives h'' < 0 at the mode
     (Lemma 13).
3. **What is not written in full.** Lemma 12 (tail sums of kernel differences in the bulk) is
   given as a proof outline, a chain of standard splits. I classify it as routine, but it has
   not been checked line by line. Everything else is written as a proof.
4. **Strongest statement without (EQ)** (Theorem 1′, §6): the exact sign pattern holds outside
   two sets, |x_{N,k}| ≤ R and the window KB_N ≤ L ≤ Kλ_NB_N on the side of the smaller scale.
   The plan's "eventual, not uniform" caveat is confirmed.
5. **Numerics** (§7): six of the seven predictions held, and three of them only after
   corrections. R2's range was badly chosen; read on fixed exponent ranges, it holds. R4's ratio
   converges in L/B_N, not in N. R6 gave 17 modes at N = 1000, not 16, and the count settles at 15
   from N = 2500.

## 1. The theorem

Notation follows F. D_N(j) = P_N(N−j−1) − P_N(N−j), Δ is the forward difference,
Λ_N = a_−(N), x_* = (2α_+s)^{−1/α_−}, x_{N,k} = (k − pN)/B_N, and L = L_k = (k − pN)/(1−p).
Modes and minima use F's block convention (`sec:extrema`).

**Hypotheses.**
- (SPAN) and (LR) for both signs. (LR) implies (RV).
- (LD2) for both signs: |f_σ(n+1) − 2f_σ(n) + f_σ(n−1)| ≤ C f_σ(n)/n².
- (EQ): c ≤ T_+(n)/T_−(n) ≤ C for large n. Then α_+ = α_− = α, a_+ ≍ a_−, and b_{+,N} ≍ b_{−,N} ≍ B_N.
- The start is fresh with either sign, or fair.
- No ties: κ̃_+(j+1) ≠ κ̃_+(j) for 0 ≤ j < J_+, where u_− is strictly decreasing on
  [J_+, ∞) (`lem:diff-renewal`). The same holds at the minus end.

**Theorem 1 (exact eventual mode count).** Under these hypotheses, fix
η ∈ (0, 1 − 1/α) and η' ∈ (0, x_*). For all large N the sign of D_N(j) on 0 ≤ j < N − pN is
as follows, read from the plus end towards the bulk.
- (i) On 0 ≤ j < J_+, the sign of κ̃_+(j+1) − κ̃_+(j).
- (ii) On J_+ ≤ j ≤ (x_*−η')Λ_N, negative.
- (iii) On the window ((x_*−η')Λ_N, (x_*+η')Λ_N), D_N is strictly increasing. So it changes sign
  exactly once and vanishes at most once.
- (iv) On (x_*+η')Λ_N ≤ j ≤ (1−p)N − K_0B_N, positive, for a K_0 that depends only on the laws.
- (v) On |x_{N,k}| ≤ R, with R = (1−p)K_0 + 1, the sign of ΔP_N(k) = P_N(k+1) − P_N(k) changes
  exactly once, at a k with x_{N,k} → the mode of h_N. Next to that change ΔP_N is strictly
  decreasing.

The mirror statements hold at the minus end. Consequently P_N has exactly M_+ + M_− + 1 modes:
- M_+ copies of the local maxima of κ̃_+;
- one antimode (a local minimum) at each end;
- one bulk mode;
- M_− copies at the minus end.

It has exactly three modes for all large N if and only if each κ̃_± has one local maximum. For a
fresh or fair start, that is the case if and only if u_∓ is nonincreasing on j ≥ 1. For example,
it holds for log-convex laws (`lem:logconvex`).

*Proof of the consequence.* Zones (i)–(v) and their mirrors cover 0 ≤ k ≤ N with overlaps at
every junction (§5). The sign sequence of D_N therefore has the following form:
- the signs of Δκ̃_+ up to J_+;
- then − up to the window, then exactly one change to + (a plateau of at most two points is
  counted once);
- + up to the bulk change, where P_N has its maximum block;
- − on the minus side up to the minus window, exactly one change;
- then the signs of the minus profile.

Since κ̃_+ is strictly decreasing on [J_+, ∞), its local maxima all lie in [0, J_+], and each of
them corresponds to exactly one local maximum of P_N. Counting the maxima gives
M_+ + 1 + M_−. ∎

The proof of (i), (ii) and the parity in (iii) is `thm:ends`, which needs (LR) and (LD) for both
signs; Lemma 2 below gives (LD). The proof of (iii) is in §3, of (iv) in §4 and of (v) in §5.

## 2. Two elementary lemmas

**Lemma 2.** If f is positive and satisfies (LR) and (LD2), then (LD) holds, and also
(LR2): f(n) − f(n+1) = (α+1+o(1)) f(n)/n.

*Proof.*
- **(LD).** Δf(M) → 0, so Δf(n) = −Σ_{i≥n}Δ²f(i). Hence
  |Δf(n)| ≤ CΣ_{i≥n} f(i)/i² ≤ C' f(n)/n, because f ∈ RV_{−α−1}.
- **(LR2).** Put r(n) = nΔf(n)/f(n), which is bounded. For λ > 1 and k = ⌊(λ−1)n⌋,
  |Δf(n+i) − Δf(n)| ≤ C i f(n)/n² for i ≤ k. Summing over i < k,
  f(n+k)/f(n) − 1 = (λ−1)r(n) + O((λ−1)²).
- By regular variation the left side tends to λ^{−α−1} − 1. So
  limsup_n |r(n) − (λ^{−α−1}−1)/(λ−1)| ≤ C(λ−1).
- Letting λ ↓ 1 gives r(n) → −(α+1). ∎

**Lemma 3 (second-difference renewal theorem).** Assume (RV), (SPAN) and (LR) for the minus
sign. Put t_n = T_−(n+1), d_n = u(n) − u(n−1) and ∇a_n = a_n − a_{n−1} (with a_{−1} = 0).
Then:
- n∇d_n/t_n → α_−/μ_−², that is, u(j+1) − 2u(j) + u(j−1) ~ f_−(j)/μ_−²;
- ∇d ∈ ℓ¹;
- the sequence d∗d is in ℓ¹ and is O(t_n). In particular Δ²v_−(j) = O(T_−(j)), and Δ²ṽ ∈ ℓ¹
  for ṽ = v_− extended by 0.

(LD) is not needed.

*Proof.* This repeats the proof of `lem:diff-renewal` in a smaller algebra.
- **The algebra.** Put ‖a‖_{t'} = sup_{n≥1} n|∇a_n|/t_n and 𝔅 = {a : ‖a‖_1 + ‖a‖_t + ‖a‖_{t'} < ∞}.
- **The difference of a product.** Splitting the convolution at M = ⌊n/2⌋ gives
  ∇(a∗b)_n = Σ_{k≤M} a_k∇b_{n−k} + Σ_{l≤n−M−1} b_l∇a_{n−l} + a_{M+1}b_{n−M−1}.
  The last term is at most ‖a‖_t‖b‖_t t_{n/2}², and n t_{n/2}²/t_n → 0. Hence
  ‖a∗b‖_{t'} ≤ C(‖a‖_1‖b‖_{t'} + ‖a‖_{t'}‖b‖_1 + ‖a‖_t‖b‖_t).
- **The product rule.** If n∇a_n/t_n → χ'_a and n∇b_n/t_n → χ'_b, then by dominated convergence
  (exactly as in `eq:product-rule`) n∇(a∗b)_n/t_n → â(1)χ'_b + b̂(1)χ'_a.
- **The data.** (LR) gives n∇t_n/t_n = −nf_−(n)/T_−(n+1) → −α, so χ'_t = −α.
- **Inversion.** In the truncation of `lem:diff-renewal` take M so large that the
  Neumann-series constant is at most 1/4 also for the new norm. Then:
  - e has geometric decay, so χ'_e = 0;
  - g = e∗t'' has χ'_g = ê(1)χ'_t;
  - ‖g^{∗k}‖_{t'} ≤ Ck²4^{−k};
  - by induction, χ'(g^{∗k}) = kĝ(1)^{k−1}χ'_g;
  - h = Σ(−g)^{∗k} has χ'_h = −χ'_g/(1+ĝ(1))².
- **Conclusion.** From d = e + e∗h,
  χ'_d = ê(1)χ'_h = −ê(1)²χ'_t/(1+ĝ(1))² = α/μ². Summability follows from |∇d_n| ≤ Ct_n/n.
- **The last claim.** The generating function of ∇²(u∗u) is (1−z)²Û² = D̂², so
  ∇²(u∗u) = d∗d. By the product rule for χ, (d∗d)_n/t_n → 2d̂(1)χ_d = −2/μ³. Since
  u∗u = v + u (`eq:conv-v` with the term i = j), Δ²v = (d∗d)(·+2) − Δ²u = O(T_−(j)). ∎

Check: `py -I check04_renewal_bigjump.py` (R1). For the zeta law the ratio μ²Δ²u(j)/f(j) is
0.943, 0.994, 0.9994 and 0.9997 at j = 10, 10², 10³ and 10⁴. For runs ≥ 2 it is 0.985, 0.998 and
0.9999 at j = 10², 10³ and 10⁴, and Δ²u changes sign for the last time at j = 18.

## 3. Step (b): one antimode

### 3.1 Plus runs at second order

Write f = f_+, μ = μ_+, V_m = f^{∗m}, δX_m = X_{m+1} − X_m (a difference in the index),
∇X(n) = X(n−1) − X(n), ∇²X(n) = X(n−2) − 2X(n−1) + X(n), and q_m = q^+_m. Uniformity is over
0 ≤ m ≤ n^{1−η}, as in `lem:plus-diff`.

**Lemma 4.** Assume (LR) and (LD2) for the plus sign, and fix η ∈ (0,1). Uniformly in
0 ≤ m ≤ n^{1−η}:
- (v) |∇²V_m(n)| ≤ Cmf(n)/n² (for m ≥ 1);
- (vi) |∇δV_m(n)| ≤ Cf(n)/n;
- (vii) |δ²V_m(n)| ≤ Cf(n)/n;
- (viii) |q_{m+3}(n) − 2q_{m+2}(n) + q_{m+1}(n)| ≤ Cf(n)/n.

*Proof.* Items (i)–(iv) of `lem:plus-diff` are used freely.

**(v).** Repeat the proof of `lem:plus-diff`(ii) with three points.
- **No giant summand.** Choose K_0 with (K_0/4 − 1)(α−1)/2 > α + 4. The event has probability
  at most n^{−α−4} at each of n−2, n−1 and n, which is o(f(n)/n²).
- **First giant index I = i.** The second difference of Σ_z h_i(z) f(n'−z) 1{n'−z ≥ w} is
  Σ_{z≤n−2−w} h_i(z)Δ²f(n−1−z) plus two boundary terms:
  - the main sum is at most Cf(n)/n² by (LD2) at arguments ≥ n/K_0;
  - the first boundary term is h_i(n−1−w)(f(w+1) − f(w)), which is at most Cmf(n)·f(n)/n;
  - the second is f(w)[h_i(n−w) − h_i(n−1−w)].
- **The second boundary term.** h_i is the law of a sum of m−1 independent variables, i−1 of
  them truncated below w. At levels ≥ n/2 the proof of (ii) applies to it verbatim, since a
  truncated variable is never a giant at threshold w and `lem:truncated` only improves under
  truncation. So |∇h_i| ≤ Cmf(n)/n there, and the term is at most Cmf(n)²/n.
- Summing over i ≤ m gives Cmf/n² + Cm²f²/n. Since nf(n) ≤ CT(n) → 0, the claim follows.

**(vi).** δV_m = f∗V_m − V_m, so ∇δV_m(n) = Σ_x f(x)[∇V_m(n−x) − ∇V_m(n)].
- **x ≤ n/2.** By (v) the bracket is at most Cxmf(n)/n². This part is at most
  Cμmf/n² ≤ Cf/n.
- **x > n/2.** The term ∇V_m(n)Σ_{x>n/2}f(x) is at most Cmf(n)T(n)/n.
- What remains is Σ_{y<n/2} f(n−y)[V_m(y−1) − V_m(y)]. Summation by parts turns it into
  Σ_y V_m(y)∇f(n−y) plus a boundary term f(n/2)V_m(n/2). The sum is at most Cf/n by (LD), and the
  boundary term is at most Cmf². (For m = 0, ∇δV_0(n) = ∇f(n) for n ≥ 2.)

**(vii).** δ²V_m(n) = Σ_x f(x)[δV_m(n−x) − δV_m(n)].
- **x ≤ n/2.** By (vi) the bracket is at most Cxf/n, and this part is at most Cμf/n.
- **x > n/2.** The term δV_m(n)Σ_{x>n/2}f is O(fT).
- What remains is Σ_{y<n/2} f(n−y)δV_m(y). It equals
  E[g(S_m+X) − g(S_m)] + f(n)Σ_{y<n/2}δV_m(y), with g(y) = (f(n−y) − f(n))1{0 ≤ y < n/2} and X an
  independent copy of X_+.
  - If both arguments of g are below n/2, then |g(a+x) − g(a)| ≤ Cxf/n by (LD).
  - If a < n/2 ≤ a + x, then |g(a)| ≤ Cf. This event has probability q_{m+1}(⌈n/2⌉) ≤ CT(n).
  - Σ_{y<n/2}δV_m(y) = −q_{m+1}(⌈n/2⌉) = O(T(n)).
- Total: Cμf/n + CfT.

**(viii).** Put δq_{m+1} = q_{m+2} − q_{m+1}. Then δq_{m+1}(n) = Σ_x f(x)[q_{m+1}(n−x) − q_{m+1}(n)]
(the proof of (iv)), and ∇δq_{m+1}(l) = δ²V_m(l−1). So the second index difference is
Σ_x f(x)[δq_{m+1}(n−x) − δq_{m+1}(n)].
- **x ≤ n/2.** By (vii) this part is at most Cμf/n.
- **x > n/2.** The term δq_{m+1}(n)Σ_{x>n/2}f is O(fT).
- What remains is Σ_{y<n/2} f(n−y)δq_{m+1}(y). Split it as
  Σ_{y<n/2}[f(n−y) − f(n)]δq_{m+1}(y) + f(n)Σ_{y<n/2}δq_{m+1}(y).
- **First part.** δq_{m+1} = f∗q_{m+1} − q_{m+1}, with q_{m+1} = 0 at arguments ≤ 0. Hence
  Σ_y g(y)δq_{m+1}(y) = Σ_x f(x)Σ_{y'} q_{m+1}(y')[g(y'+x) − g(y')]. This is at most
  Cμ·(Σ_{y'} q_{m+1}(y'))·f/n plus a crossing term at most C f T(n).
  Here Σ_y q_{m+1}(y) = μ.
- **Second part.** Σ_{y≥L'}q_{m+2}(y) = Σ_x f(x)G(L'−x), with G(L') = Σ_{y≥L'}q_{m+1}(y). So
  |Σ_{y≥L'}δq_{m+1}(y)| ≤ Σ_x f(x)Σ_{L'−x≤y<L'} q_{m+1}(y) ≤ CT(L') by (i), and the full sum of
  δq_{m+1} is 0. So this part is f(n)O(T(n)). ∎

### 3.2 Second differences in the layer

**Theorem 5.** Assume (RV), (SPAN) and (LR) for the minus sign, and (LR) and (LD2) for the plus
sign. Fix η ∈ (0,1) and let the start be fresh, or a mixture of the two fresh starts. Then,
uniformly in 1 ≤ j ≤ N^{1−η},

  P_N(N−j−2) − 2P_N(N−j−1) + P_N(N−j) = T_+(N)Δ²u_−(j) + O( f_+(N)(T_−(j) + 1/N) ).

*Proof.* Take the plus start; the minus start is §3.3, and mixtures follow by linearity.
- **The identity.** Use the exact identity of `thm:first-diff`'s proof,
  P_N(N−j) = Σ_m [a_m(j)Q_m(n) + V_m(n)b_m(j)] with n = N−j, a_m = u^−_m, Q_m = q_{m+1},
  b_m = q^−_m. Only m ≤ j+3 occurs, and Lemma 4 applies at arguments ≥ N/2 with η/2.
- **The six parts.** Differencing D_N = I + II + III + IV once more in j (so n moves to n−1)
  gives ΔD_N = A1 + 2A2 + A3 + 2A4 + A5 + A6, where:
  - A1 = Σ Δ²a_m(j)Q_m(n−2);
  - A2 = Σ Δa_m(j)δV_m(n−2), since ∇Q_m = δV_m(·−1);
  - A3 = Σ a_m(j)∇δV_m(n−1);
  - A4 = Σ ∇V_m(n−1)Δb_m(j);
  - A5 = Σ ∇²V_m(n)b_m(j);
  - A6 = Σ V_m(n−2)Δ²b_m(j).
- **The minus-side facts used.**
  - Ā_i = Σ_{m>i}a_m, with Σ_i|ΔĀ_i(j)| ≤ 1 + ‖d‖_1 (`thm:first-diff`, fact 2).
  - W_i(j) = Σ_{m≥i+2}(m−1−i)a_m(j) = Σ_x u^−_{i+1}(x)ṽ(j−x).
  - B̄_i(j) = Σ_{m>i}b_m(j) = P(S^−_i < j), so ΔB̄_i = u^−_i(j) and Δ²B̄_i = Δa_i(j).
  - Σ_m b_m = 1 and Σ_m m b_m ≤ j.
- **A5.** By (v) it is at most Cf(N)j/N² ≤ Cf/N.
- **A3.** By (vi) it is at most Cf u(j)/N.
- **A4.** It equals Σ_i ∇δV_i(n−1)u^−_i(j), since Σ_mΔb_m = 0, and is at most Cf/N by (vi).
- **A6.** It equals Σ_i δV_i(n−2)Δa_i(j), which has the same form as A2.
- **A2.** Summation by parts gives δV_1Δu(j) + Σ_i δ²V_i ΔĀ_i(j). This is O(fT_−(j)) + O(f/N),
  by (vii) and fact 2.
- **A1.** Two summations by parts, with Q_m = Q_1 + (m−1)δQ_1 + Σ_{i≤m−2}(m−1−i)δ²Q_i, give
  A1 = Q_1(n−2)Δ²u(j) + δQ_1(n−2)Δ²(v−u)(j) + Σ_{i≥1}δ²Q_i(n−2)Δ²W_i(j).
  - Q_1(n−2) = q_2(N−j−2) = T_+(N) + O(jf). Combined with j|Δ²u(j)| ≤ CT_−(j) (Lemma 3), the
    first term is T_+(N)Δ²u(j) + O(fT_−(j)).
  - δQ_1 = O(f) by (iv), and Δ²(v−u) = O(T_−(j)) by Lemma 3.
  - |δ²Q_i| ≤ Cf/N by (viii), and Σ_i|Δ²W_i(j)| ≤ Σ_x u(x)|Δ²ṽ(j−x)| ≤ ‖Δ²ṽ‖_1.
- Adding up gives the theorem. ∎

### 3.3 The minus start

- Q_m = q^+_m and b_m = q^−_{m+1}, so Q_1 = T_+(n), Σ_mΔb_m = f_−(j) and Σ_mΔ²b_m = Δf_−(j).
- The extra terms are ∇V_1·f_−(j) = O(f/N) in A4 and V_1Δf_−(j) = O(f·f_−(j)) in A6.
- The index shift turns δV_i into δV_{i−1} and δ²Q_i into δ²Q_{i−1}. Lemma 4 covers m = 0.
- The rest is unchanged.

### 3.4 Convexity and the single antimode

**Corollary 6.** Let J_0 be such that Δ²u_− > 0 on [J_0, ∞); it exists by Lemma 3. For every
K, for all large N, j ↦ P_N(N−j) is strictly convex on J_0 ≤ j ≤ KΛ_N. That is, D_N is strictly
increasing there.

*Proof.* By Lemma 3, T_+(N)Δ²u(j) ≥ T_+(N)f_−(j)/(2μ_−²). Also f_+(N) ≤ CT_+(N)/N. It is
therefore enough to have N f_−(j)/T_−(j) → ∞ and N²f_−(j) → ∞ uniformly on [J_0, KΛ_N].
- The first ratio is ≍ N/j ≥ N/(KΛ_N) → ∞.
- For the second, N²f_−(KΛ_N) ≍ N·NT_−(KΛ_N)/(KΛ_N) ≍ K^{−α−1}N/Λ_N → ∞. ∎

**Theorem 7 (step (b)).** Under the hypotheses of `thm:ends` together with (LD2) for the plus
sign, for all large N, D_N is strictly increasing on the window of `thm:ends`(d). So D_N changes
sign exactly once there and vanishes at most once. This is part (iii) of Theorem 1, and it does
not use (EQ).

*Proof.* The window lies in [J_0, (x_*+1)Λ_N] for large N. Apply Corollary 6 and
`thm:ends`(d). ∎

The convexity range is wider: the error is dominated as long as N²f_−(j) → ∞, which holds up to
j = N^{2/(α_−+1)−ε}. Numerically, convexity holds from j = 0 to x ≈ 1.4 in units of B_N (R3, §7).

## 4. Step (c): the big-jump zone

### 4.1 The difference form of the local big-jump theorem

Write f = f_+, μ = μ_+, a = a_+, V_m = f^{∗m}, and L = n − mμ.

**Lemma 8 (local big jump for differences).** Assume (LR) and (LD2) for the plus sign. For every
ε > 0 there is K such that, for all m ≥ 1 and all n with L ≥ Ka(m),
- (D1) |∇V_m(n) − m(α+1)f(L)/L| ≤ ε m f(L)/L;
- (D0) V_m(n) ≤ C m f(L);
- (D2) δV_m(n) = [f(L) + μ(α+1)m f(L)/L](1+θε);
- (D3) q_{m+2}(n) − q_{m+1}(n) = [2μf(L) + μ²(α+1)m f(L)/L](1+θε), for m ≥ 0;

with |θ| ≤ 1. Moreover q_{m+1}(n) ≤ C(T(L) + m f(L)). In (D2) and (D3), L and the order of
quantifiers are the same as in (D1).

No restriction m ≤ n^{1−η} is imposed. This is the point of the lemma: the zone needs m ≍ N.

*Proof of (D1).* For m = 1 this is (LR2), by Lemma 2. Let m ≥ 2. Fix a small δ > 0, depending
only on α, and put w = ⌈δL⌉.

**(1) No summand ≥ w.** Write f_w = f1{·<w} and m = m_1 + m_2 with m_1 = ⌊m/2⌋. Then
∇(f_w^{∗m})(n) = Σ_y f_w^{∗m_1}(y)∇f_w^{∗m_2}(n−y). Split the sum at y_0 = m_1μ + L/2. For
y < y_0, sum by parts so that the difference falls on f_w^{∗m_1}. Each piece is then bounded as
follows.
- A uniform bound for the difference: sup_x|∇f_w^{∗m'}(x)| ≤ Ca(m)^{−2}. This is Fourier
  inversion. We have |φ_w(t)| ≤ |φ(t)| + T(w) and 1 − |φ(t)| ≥ cT(1/|t|) on |t| ≤ π, by (SPAN)
  and Karamata. Also m'T(w) ≤ C_δK^{−α} is bounded. So
  ∫|t|(|φ| + T(w))^{m'}dt ≤ C/w² + C/a(m')² ≤ C/a(m)².
- A truncated deviation probability P(S^{(w)}_{m_i} − m_iμ ≥ L/2 − μ). By `lem:truncated` it is
  at most C(mT(δL))^{1/(5δ)}.
- The boundary term of the split, a product of two such local probabilities, which is smaller.

By Potter's bounds, mT(δL) ≤ C_δ(L/a(m))^{−α+ε'} and m f(L)/L ≥ c(L/a(m))^{−α−ε'}/L². So the
no-giant part is o(m f(L)/L) as K → ∞, provided δ < (α−ε')/(5(α+2+ε')).

**(2) A giant summand.** Let I be the first index with X_I ≥ w, and h_i as in `lem:plus-diff`(ii).
The n-difference of P(S_m = ·, I = i) is
Σ_{z≤n−1−w} h_i(z)∇f(n−z) − h_i(n−w)f(w), with ∇f(y) = f(y−1) − f(y).
- **Main range |z − (m−1)μ| ≤ εL.** Here n − z = L(1 + O(ε)) + O(μ). By (LR2) and the uniform
  convergence theorem, ∇f(n−z) = (α+1)(f(L)/L)(1 + o(1)) as ε → 0 and L → ∞.
- **The mass of the main range.** It lies between (1−T(w))^{i−1} − P(|S_{m−1} − (m−1)μ| > εL)
  and (1−T(w))^{i−1}.
- **Off the main range.** We have n − z ≥ w = δL, so |∇f(n−z)| ≤ C_δ f(L)/L by (LD) and
  Potter's bounds. The mass is at most P(|S_{m−1} − (m−1)μ| > εL).
- **That probability.** It is at most CmT(εL) + e^{C_−}e^{−εL/a(m)}. The right tail uses
  `lem:truncated` at threshold εL/8 together with a union bound, and the left tail uses
  `lem:stable`(iv). As K → ∞ this is o(1).
- **The sum over i.** Σ_{i≤m}(1−T(w))^{i−1} = m(1 + O(mT(w))) = m(1 + o_K(1)).
- **The boundary term.** h_i(n−w) ≤ P(S_{m−1} = n−w). The deviation of that point is at least
  L/2, so `lem:stable`(iii) bounds it by CmT(L)/a(m). Summed over i, the boundary terms are at
  most Cm²T(L)f(L)/a(m). Relative to m f(L)/L this is CmT(L)L/a(m) ≤ C(L/a(m))^{1−α+ε'} → 0.

The same decomposition without differences gives (D0). ∎

*Proof of (D2).* δV_m(n) = Σ_x f(x)[V_m(n−x) − V_m(n)]. Fix ε_1 > 0.
- **x ≤ ε_1L.** The bracket is Σ_{i<x}∇V_m(n−i). By (D1) at deviations ≥ (1−ε_1)L it equals
  x m(α+1)(f(L)/L)(1 + o(1)). With Σ_{x≤ε_1L} x f(x) → μ this part is μ(α+1)m f(L)/L·(1 + o(1)).
- **x > ε_1L.** The term V_m(n)T(ε_1L) is at most Cm f(L)T(ε_1L), which is o(m f(L)/L) since
  T(y)y → 0. The remaining part is E[f(n−S_m); n − S_m > ε_1L].
  - On |S_m − mμ| ≤ ε_2L it is f(L)(1 + o(1)), and this event has probability 1 − o(1).
  - On S_m − mμ > ε_2L it is at most C_{ε_1}f(L), with probability at most CmT(ε_2L) = o_K(1).
  - On S_m − mμ < −ε_2L it is at most Cf(L), with probability at most e^{−cε_2K}. ∎

*Proof of (D3).* Write δq_{m+1}(n) = Σ_x f(x)[q_{m+1}(n−x) − q_{m+1}(n)].
- **x ≤ ε_1L.** The bracket is Σ_{l=1}^{x}δV_m(n−l). By (D2) this part is
  μ[f(L) + μ(α+1)m f(L)/L](1 + o(1)).
- **x > ε_1L.** The term q_{m+1}(n)T(ε_1L) is at most C(T(L) + m f(L))T(ε_1L) = o(f(L) + m f(L)/L).
- The remaining part is E[Σ_{y=S_m+1}^{S_{m+1}} f(n−y)1{n−y > ε_1L}]. On
  {|S_m − mμ| ≤ ε_2L, X_{m+1} ≤ ε_2L} it equals X_{m+1}f(L)(1 + o(1)). Its expectation on that
  event tends to μ, since X_{m+1} is independent of S_m and E[X; X > ε_2L] → 0.
- The complement contributes at most C f(L)(E[X; X > ε_2L] + μP(|S_m − mμ| > ε_2L)) = o(f(L)).
- **The bound on q_{m+1}.** Split q_{m+1}(n) = Σ_x V_m(x)T(n−x) at x = n − L/2. The lower part is
  at most T(L/2), and the upper part at most Cm f(L)μ by (D0). ∎

**Check of (D1)** (`py -I check04_renewal_bigjump.py`, R7). For the zeta law the ratio
∇V_m(n)/[m(α+1)f(L)/L] at K = L/a(m) = 5, 10, 20, 40 and 80 is:
- m = 10: 0.34, 0.65, 0.86, 0.94, 0.98;
- m = 100: 0.37, 0.73, 0.92, 0.98, 0.99;
- m = 1000: 0.42, 0.80, 0.95, 0.99, 0.997.

So the limit is reached as K → ∞, uniformly in m, as the lemma says.

### 4.2 Assembly

Put 𝒟_N(j) = 2s f_+(L)/μ_−² + (j s²/μ_−³)(α_+ + 1) f_+(L)/L, where L = L_{N−j} = N − js/μ_−.
For the plus start this is (1 + o(1))∂_jG_N: differentiate `eq:G` with γ(j) ~ js/μ_−² and
u_−(j) → 1/μ_−.

**Theorem 10 (difference form of Theorem B).** Assume (SPAN) and (LR) for both signs, (LD2) for
the plus sign and (EQ), and let the start be fresh of either sign or fair. Fix
η ∈ (0, 1 − 1/α_−). Then

  lim_{K→∞} limsup_{N→∞} sup_{N^{1−η} ≤ j ≤ (1−p)N − KB_N} |D_N(j)/𝒟_N(j) − 1| = 0.

In particular there is K_0 with D_N > 0 on that range for all large N. This is part (iv) of
Theorem 1, together with `thm:ends`(c).

*Proof.* Take the plus start, and write n = N−j, i_0 = j/μ_−, L = L_{N−j} and
L_m = n − 1 − mμ_+, so that L_{i_0} = L − 1. Use D_N = I + II + III + IV after the summations by
parts of `thm:first-diff`, which are exact for every j ≥ 1:
- I = Q_1(n−1)Δu(j) + Σ_i δQ_i(n−1)ΔĀ_i(j);
- II = Σ_m u^−_m(j)δV_m(n−1);
- III = Σ_i δV_i(n−1)u^−_i(j);
- IV = Σ_m ∇V_m(n)q^−_m(j).

Here δQ_i = q_{i+2} − q_{i+1}. Fix M, then K, then N.

**Index classes.**
- **Window:** W = {m : |m − i_0| ≤ Ma_−(j)}.
  - There L_m = L(1 + O(M/K)), since L ≥ KB_N ≥ cKa_−(j), and m = i_0(1 + o(1)).
  - Also L_m ≥ Ka_+(m)/2, since a_+(m) ≤ CB_N.
  - So Lemma 8 gives each plus factor at (i_0, L) up to a factor 1 + o(1).
- **Left of W:** L_m > L. Lemma 8 gives |∇V_m| ≤ Ci_0 f(L)/L, δV_m ≤ C(f(L) + i_0 f(L)/L), and the
  same for δQ_m. By `lem:index`(a), Σ_{m∉W}u^−_m(j) and Σ_{m∉W}q^−_m(j) are at most η(M) + o(1).
  Since J(j) ≤ j+1 and its left deviations are exponentially rare,
  Σ_{m∉W} m q^−_m(j) ≤ i_0(η'(M) + o(1)).
- **Right of W, with m ≤ m_* = i_0 + L/(2μ_+):** L_m ≥ L/2, so the same bounds and the same
  small masses apply.
- **Bad indices m > m_*:** mμ_− − j ≥ cL, a left deviation of the minus sum.
  - By `lem:stable`(iv) applied to one half of the sum, u^−_m(j) and q^−_m(j) are at most
    (C/a_−(m))e^{−c(mμ_−−j)/a_−(m)}.
  - The plus factors are crudely bounded by Lemma 11 below: |∇V_m| ≤ C/a_+(m)²,
    |δV_m| ≤ μ sup|∇V_m| and |δQ_m| ≤ μ sup|Δq_{m+1}| ≤ C/a_+(m)².
  - By (EQ), a_±(m) ≍ a(j) for i_0 ≤ m ≤ j+1. So the bad indices contribute at most
    Ca(j)^{−2}e^{−cL/a(j)} to each part.
  - With r = L/a(j) ≥ cK we have 𝒟_N ≥ c i_0 f(L)/L ≥ c r^{−α−2−ε}a(j)^{−2}. The ratio of the bad
    contribution to 𝒟_N is at most Cr^{α+2+ε}e^{−cr} → 0.

**The parts.**
- **IV** = (α+1)(f(L)/L)Σ_{m∈W} m q^−_m(j)(1 + o(1)) + o(i_0 f/L) = (α+1)i_0 f(L)/L·(1 + o(1)).
  This uses EJ(j) = Σ_m m q^−_m(j) ~ i_0.
- **II and III** each equal u(j)[f(L) + μ_+(α+1)i_0 f(L)/L](1 + o(1)), with u(j) → 1/μ_−.
- **I.**
  - The first term: Q_1(n−1) = q_2(n−1) ≤ CT_+(N) and |Δu(j)| ≤ CT_−(j), so it is O(T_+(N)T_−(j)).
    Since η < 1 − 1/α_−, NT_−(N^{1−η}) → 0, so the term is o(f_+(N)) = o(f(L)).
  - The second term: write Σ_i δQ_iΔĀ_i(j) = δQ_{i_0}Δ(v−u)(j) + Σ_i(δQ_i − δQ_{i_0})ΔĀ_i(j).
  - Here Δ(v−u)(j) → 1/μ_−². For the error, ΔĀ_i(j) = Σ_{x<j}u^−_i(x)d_{j+1−x} + u^−_i(j)u(1).
    - For j − x ≤ R', the index i lies in a window of width Ma_−(j) + R'/μ_− around i_0, up to a
      small mass, so |δQ_i − δQ_{i_0}| = o(f + i_0 f/L).
    - For j − x > R', the contribution is at most (Σ_{r>R'}|d_r|)·C(f + i_0 f/L). This uses
      Σ_i u^−_i(x)|δQ_i| ≤ C(f + i_0 f/L) for x ≤ j, by the index classes at level x.
  - So I = [2μ_+f + μ_+²(α+1)i_0 f/L]/μ_−² + o(f + i_0 f/L).

**Total.** Adding up,

  D_N = f(L)[2μ_+/μ_−² + 2/μ_−] + (α+1)i_0(f(L)/L)[μ_+²/μ_−² + 2μ_+/μ_− + 1] + o(…)
      = 𝒟_N(j)(1 + o(1)),

since 2μ_+/μ_−² + 2/μ_− = 2s/μ_−² and (μ_+ + μ_−)²/μ_−² = s²/μ_−².

**Other starts.** The minus start differs by index shifts and by the term V_1(n−1)f_−(j) in III,
which is O(f_+(N)f_−(j)). The leading terms are the same. The fair start follows by linearity.
∎

At j = N^{1−η}, 𝒟_N ~ 2sf_+(N)/μ_−² = c_aT_+(N)/(α_+N). This matches the limit of
`thm:first-diff`, so the two zones join consistently.

**Where (EQ) enters.** Only through the bad indices. Without (EQ) the same estimate needs
e^{−cL/a_−(j)} to beat (a_−(j)/a_+(j))². That holds on L ≥ Kλ_NB_N with λ_N as in `eq:lambdaN`,
and the window of F (`thm:window`) is exactly where it fails.

## 5. Step (a): the bulk

### 5.1 Differences of the kernels

**Lemma 11 (local limits for differences).** Assume (RV) and (SPAN) for the sign σ, let 𝗄 be a
kernel of sign σ (u_m, q_m or q_{m+1}), and let r ∈ {1,2}. Then
sup_j |a(m)^{1+r}Δ^r𝗄_m(j) − c_𝗄 g^{(r)}((j−mμ)/a(m))| → 0, and
sup_{m,j} a(m)^{1+r}|Δ^r𝗄_m(j)| < ∞.

*Proof.* This is Gnedenko's proof (`lem:stable`(ii), Ibragimov–Linnik Thm 4.2.1) with the extra
factor (e^{−it} − 1)^r.
- **The formula.** Δ^r u_m(j) = (2π)^{−1}∫_{−π}^{π}φ(t)^m(e^{−it} − 1)^r e^{−itj}dt.
- **Outer range.** On ε ≤ |t| ≤ π, (SPAN) gives |φ| ≤ e^{−c}, so this range contributes
  O(e^{−cm}).
- **Inner range.** Put t = θ/a(m) and recentre. Then ψ(θ/a)^m → exp(K_α(−iθ)^α) and
  a(m)(e^{−iθ/a} − 1) → −iθ. The integrand is dominated by |θ|^r exp(−c|θ|^{α−δ}): Potter's
  bounds together with 1 − |φ(t)| ≥ cT(1/|t|).
- **Uniformity in j.** The phase e^{−iθy} has modulus one, so the limit is uniform in j and
  equals g^{(r)}(y).
- **The q kernels.** q_m = u_{m−1}∗τ with τ(v) = T(v)1{v≥1}, whose Fourier transform τ̂ is
  continuous, bounded by μ, and equals μ at 0. The same proof applies with the factor τ̂(θ/a) → μ.
  The same holds for q_{m+1}.
- **The uniform bound.** For large m it follows from the domination. Finitely many m are trivial.
  ∎

**Lemma 12 (tails of kernel differences).** Proof in outline only. Assume (RV), (SPAN) and (LD)
for the sign σ, and let r ∈ {1,2}. For j → ∞ and K ≥ 2:
- (T2) Σ_{m∉I^σ_j(K)} |Δ^r𝗄_m(j)| ≤ (ε_r(K) + o(1)) a_σ(j/μ_σ)^{−r}, with ε_r(K) → 0;
- (T1) for levels j ≍ N, sup_m a_σ(N)^{1+r}|Δ^r𝗄_m(j)| is bounded over m ≥ εN, and
  Σ_{m<εN}|Δ^r𝗄_m(j)|·𝗄'_m ≤ o(a_σ(N)^{−1−r}) for any weights 𝗄'_m ≤ 1. This second part uses the
  r-th difference version of (D0)–(D1), |∇^rV_m(n)| ≤ Cm f(L)/L^r. That version needs (LD2) for
  r = 2, with the proof of Lemma 4(v).

*Outline.*
- **A pointwise bound.** For z = j − mμ,
  |Δ^r u_m(j)| ≤ Ca(m)^{−1−r}[P(|S_{⌊m/3⌋} − ⌊m/3⌋μ| ≥ |z|/3 − μ) + mT(|z|/3)1{z>0}].
  Write u_m as a convolution of three blocks. At least one block carries a third of the
  deviation. Put the r differences on the other blocks, moving them by summation by parts at the
  cut. Then bound those blocks by Lemma 11, sup|Δ^r(u_{m'}∗u_{m''})| ≤ Ca^{−1−r}, and the
  deviating block by its probability. The boundary terms are products of a local probability at
  the cut (`lem:stable`(iii) or (iv)) with Ca^{−r}.
- **Summing over m ∉ I.**
  - Indices m ≤ j/(2μ) give at most Cj²T(j)/a(j)^{1+r} = o(a(j)^{−r}), since 2 − α − 1/α < 0.
  - Right deviations Ka ≤ z ≤ j/2 give at most (j/a^{1+r})·KaT(Ka) ≤ CK^{1−α+δ}a^{−r}.
  - Left deviations give at most Ce^{−cK}a^{−r}.
- **q kernels.** Δ^r q_m = (Δ^r u_{m−1})∗τ. Shifts v ≤ v_0 keep the window. Shifts
  v_0 < v ≤ j/2 contribute at most (Σ_{v>v_0}T)·Ca^{−r}, using Σ_m|Δ^r u_m(i)| ≤ Ca(i)^{−r} for
  every i.
- **The shifts v > j/2** need care, because T(j)·Σ_i a(i)^{−2} is not o(a(j)^{−2}) when α ≤ √2.
  Sum by parts in v instead, moving the differences onto T. Then |Δ^rT(v)| ≤ Cf(v)v^{1−r} by
  (LD), which gives O(f(j) + T(j)a(j)^{−1}) = o(a(j)^{−r}).

This is the only lemma in the report that has not been written out line by line.

### 5.2 The bulk theorem

**Lemma 13 (shape of the profile).** Let α ∈ (1,2). Under (EQ), every h_θ, θ ∈ Θ, is the
density of a nondegenerate strictly α-stable law, and the same holds for every limit point of
θ_N.
- (a) The density is real-analytic; in fact it extends to an entire function, since
  ∫e^{|t||Im z|}|e^{ψ(t)}|dt < ∞ for α > 1.
- (b) The density is bell-shaped: its n-th derivative changes sign exactly n times
  (M. Kwaśnicki, "A new class of bell-shaped functions", arXiv:1710.11023, Trans. Amer. Math.
  Soc. 373 (2020)).
  - The arXiv abstract was checked. It defines the class by "the n-th derivative of f changes its
    sign exactly n times", and states that the class includes all density functions of stable
    distributions.
  - The volume is as in the brief. The definition section of the full text was not re-read.
  - Kwaśnicki–Simon (arXiv:1910.07752) characterises the class. It is not needed here.
- (c) Consequently h_θ' has exactly one zero x_θ, the mode, and h_θ''(x_θ) < 0.
- (d) By continuity of θ ↦ h_θ in C² (dominated Fourier integrals with weight t²) and compactness
  of Θ_EQ = {θ ∈ Θ : min θ_σ ≥ θ_min}, there are uniform constants. For every R, ε there is c > 0
  with |h_θ'| ≥ c on {|x| ≤ R, |x − x_θ| ≥ ε}. There is ε_0 with h_θ'' ≤ −c on |x − x_θ| ≤ ε_0.
  The map θ ↦ x_θ is continuous.

*Proof of (c).* All derivatives tend to 0 at ±∞, by Riemann–Lebesgue. h' changes sign exactly
once, at x_θ.
- **h'' < 0 at the mode.** Suppose h''(x_θ) = 0. Then h'' ≤ 0 on (x_1, x_2), and h'' changes sign
  at x_1 < x_θ < x_2, where h' attains its maximum and minimum. Then h'' has a local maximum
  equal to 0 at x_θ. Together with the local maximum of h'' on (−∞, x_1), its local minima on
  (x_1, x_θ) and (x_θ, x_2), and its local maximum on (x_2, ∞), this gives at least five sign
  changes of h''' (analyticity makes the extrema strict), against three.
- **No other zero of h'.** A zero of h' at x_3 ≠ x_θ without a sign change is a strict local
  extremum of h', by analyticity. It adds two sign changes of h'', four in all, against two. ∎

Yamazato's unimodality alone gives neither h' ≠ 0 off the mode nor h'' < 0 at it. The bell
shape is the input that is needed.

**Theorem 14 (derivative local limit theorem in the bulk).** Assume (SPAN) and (LR) for both
signs, (LD2) and (EQ), and a fresh start (the fair start follows by linearity). For every R,
uniformly in |x_{N,k}| ≤ R,
- B_N²ΔF_N(k) = h_N'(x_{N,k}) + o(1);
- B_N³Δ²F_N(k) = h_N''(x_{N,k}) + o(1).

*Proof.* Follow Step 5 of the proof of `thm:bulk`.
- **The Leibniz expansion.** In each product 𝗄^{+,i}_m(k)𝗄^{−,i}_m(N−k) of `eq:bulk-pairs`,
  expand Δ^r: the step k → k+1 moves k_τ by ς_τ and k_τ̄ by ς_τ̄.
- **The window part.** For m ∈ I, both factors and their differences are given by Lemma 11 at
  scales a_τ(m) = B_N(1+o(1)) and a_τ̄ = θ_τ̄B_N(1+o(1)), with θ_τ̄ ≥ θ_min by (EQ).
- **The sum over m.** It is a Riemann sum with mesh μ_τ̄/b_τ̄. Its limit is
  Σ_i(c c/μ_τ̄)∫[(ς_τ∂_1 + (ς_τ̄/θ_τ̄)∂_2)^r(g_τ⊗g_τ̄)](ζ_{N,x}(y), y)dy.
- **Identification.** Integration by parts in y gives ∫∂_2Φ(ζ(y),y)dy = −(μ_τθ_τ̄/μ_τ̄)∫∂_1Φ dy.
  So inside the integral the operator acts as ς_τ(1 + μ_τ/μ_τ̄)∂_1 = d/dx. With
  Σ_i cc = s and `lem:profile`(e), the limit is h_N^{(r)}(x).
- **The tails m ∉ I.** For the τ factor, (T1) and Σ_{m∉I}𝗄^τ̄_m ≤ η(K) + o(1) give
  O(η(K))B^{−1−r}. For the τ̄ factor, 𝗄^τ_m ≤ C/B_N and (T2) give O(ε_r(K))B^{−1−r}. Mixed terms
  (r = 2, one difference on each factor) combine both bounds.
- **Errors.** Every error is a maximum over the two signs, as in `thm:bulk`. (EQ) is used so that
  the τ̄ factor errors, of order o(1)/(B_Nb_τ̄), are o(B_N^{−2}). ∎

**Corollary 15 (part (v) of Theorem 1).** For every R and all large N, ΔP_N changes sign exactly
once on |x_{N,k}| ≤ R. It has the sign of h_N' wherever |x − x_{θ_N}| ≥ ε, and it is strictly
decreasing on |x − x_{θ_N}| ≤ ε_0/2.

*Proof.* Apply Theorem 14 together with Lemma 13(d). ∎

### 5.3 Junctions

- **Copies and layer.** [0, J_+) and [J_+, …) abut. `thm:ends` handles them with J' chosen after
  η'.
- **Layer and window.** `thm:ends`(b) and (c) are applied with η'/2, so the window's end integers
  are covered twice (its proof).
- **Window and convexity.** Corollary 6 covers [J_0, (x_*+1)Λ_N], which contains the window.
- **Layer and big-jump zone.** `thm:ends`(c) holds up to N^{1−η}, and Theorem 10 holds from
  N^{1−η} on. The leading terms agree at the junction (§4.2).
- **Big-jump zone and bulk.** Theorem 10 covers L ≥ K_0B_N, that is x ≥ (1−p)K_0. Corollary 15
  covers |x| ≤ (1−p)K_0 + 1. Fix K_0 first (Theorem 10), then R, then N.
- **Minus side.** The same, with the signs exchanged.

## 6. Without (EQ): the strongest statement

**Theorem 1′.** Assume the hypotheses of Theorem 1 without (EQ). Let α_+ ≠ α_− be allowed, or
comparable indices with oscillating ratio. For all large N the sign pattern (i)–(iv) of
Theorem 1 holds at each end on:
- j ≤ (1−p)N − KB_N at the end of the larger scale;
- j ≤ (1−p)N − Kλ_NB_N at the end of the smaller scale.

Consequently, outside the bulk window |x_{N,k}| ≤ R and the window K ≤ L/B_N ≤ Kλ_N on the side
of the smaller scale, the local maxima of P_N are exactly the M_+ + M_− copies, and there is
exactly one antimode at each end. Together with `thm:modes-lower` this gives
M_+ + M_− + 1 ≤ #modes ≤ M_+ + M_− + 1 + (number of modes in the two windows).

*Proof.* Theorem 7 does not use (EQ). Theorem 10 without (EQ) holds on L ≥ Kλ_NB_N, by the remark
at the end of §4.2. At the end of the larger scale, e^{−cL/a_−(j)} ≤ e^{−cL/a_+(j)} already
suffices from L ≥ KB_N. ∎

**What is missing without (EQ).**
- (1) The bulk with θ_τ̄ → 0. The τ̄ differences need a summation by parts in the index m that I
  have not found.
- (2) The window of `thm:window`. It is open in F at the level of values too (O2).

## 7. Numerics

All runs use `py -I` from this folder. The engine is `exact04.py`, a new implementation, rows by
minus count with direct sums and no FFT.
- **Checks of the engine.** It matches a brute-force Markov chain over (count, sign, age) to
  3·10⁻¹⁶ at N = 3, 7, 15, for three starts and two laws. It matches the earlier `engine.py` to
  2·10⁻¹⁷ at N = 400.
- **Laws.** The zeta law with α = 3/2 for both signs, so (EQ) holds, and the law conditioned on
  runs ≥ 2. Both satisfy (SPAN), (LR) and (LD2).

| Pred. | Command | Prediction | Result |
|---|---|---|---|
| R1 | `check04_renewal_bigjump.py` | μ²Δ²u/f → 1; last sign change of Δ²u (runs ≥ 2) before 30 | 0.9994 at j = 10³ (zeta); last change at j = 18. **Holds** |
| R7 | same | (D1) ratio within 0.2 of 1 at K = 20 | 0.86, 0.92, 0.95 for m = 10, 10², 10³; → 1 as K grows. **Holds** |
| R2 | `check04_layer2.py` | E_N bounded on j ≤ N^{0.9} | **Range mis-chosen.** N^{0.9} reaches the bulk at N = 10³. On fixed ranges max\|E_N\| decreases in N: j ≤ N^{0.5}: 5.5, 3.3, 2.4; j ≤ N^{0.7}: 54, 33, 26 (N = 10³, 3·10³, 6·10³). Consistent with Theorem 5 |
| R3 | `check04_full.py` | convex from j = 0 to the bulk inflection | First non-convex point at x = 1.381, 1.417, 1.441 (N = 10³, 2·10³, 4·10³), against the inflection of h at 1.584. **Holds**, approaching from below |
| R4 | same | D_N > 0 on [N^{0.6}, (1−p)N − 3B_N]; ratio D_N/𝒟_N in [0.7, 1.3] | Positivity **holds** at all three N. Ratio: 1.18, 1.11, 1.07 at j = N^{0.7} (→ 1). At fixed L/B_N it is constant in N: 1.32 at L = 20B, 1.71 at L = 10B. **Partly fails:** convergence is in L/B_N, as the double limit of Theorem 10 says |
| R5 | same | sup\|B²ΔP − h'\| decreases; one sign change; Δ²P < 0 near the mode | 0.0193, 0.0149, 0.0115 (about N^{−0.37}); B³Δ²P − h'': 0.031, 0.023, 0.018; exactly one sign change on \|x\| ≤ 3; Δ²P < 0 on \|x\| ≤ 0.5. **Holds** |
| R6 | same | runs ≥ 2, fair: 16 modes at N = 10³, 15 at 3·10³ and 4·10³ | Modes 17, 19, 17, 15, 15, 15, 15 at N = 1000, 1500, …, 4000. **Count at 10³ wrong (17)**; eventual value 15 = M_+ + M_− + 1 **holds**, from N = 2500 |

**Reading of R6.**
- The second difference Δ²_jP_N(N−j) is ≤ 0 exactly at j = 11, 13, 15, 17 for every N tested.
  These are the sign changes of Δ²u_−, which stop at j = 18, inherited through Theorem 5.
- At N ≤ 2000 the antimode position x_*Λ_N lies at or below about 21. The antimode then merges
  with the tail of the profile's oscillation, and one or two extra max–min pairs appear (maxima at
  j = 14 and 16).
- From N = 2500 the antimode is at j = 25, 28, 32, 35, inside the convex range j ≥ 19, and the
  count is exactly 15.
- So the threshold N ≈ 2500 is where x_*Λ_N first exceeds J_0 = 19. That is the mechanism of
  Theorem 7. It also explains why no uniform-in-N statement is possible for general laws.

Run times: `check04_renewal_bigjump.py` a few seconds, `check04_layer2.py` about 40 s,
`check04_full.py` about 70 s and 0.5 GB.

## 8. Honest status

| Claim | Status |
|---|---|
| Lemma 2 ((LR)+(LD2) ⇒ (LD), (LR2)) | proved |
| Lemma 3 (second-difference renewal theorem) | proved; it is the same Banach-algebra argument as `lem:diff-renewal` with one more seminorm |
| Lemma 4, Theorem 5, Corollary 6, Theorem 7 (step (b): one antimode, convexity on [J_0, KΛ_N]) | proved; needs (LD2) for the plus sign, no (EQ) |
| Lemma 8 (local big jump for differences, uniform in m with L ≥ Ka(m)) | proved; this is the lemma of independent interest asked for in item 1 of the plan |
| Theorem 10 (D_N ~ ∂_jG_N on the big-jump zone) | proved under (EQ); under no (EQ) on L ≥ Kλ_NB_N |
| Lemma 11 (Fourier local limits for differences of kernels) | proved |
| Lemma 12 (tail sums of kernel differences) | **outline only**; routine splits, to be written and checked |
| Lemma 13 (bell shape, h'' < 0 at the mode) | proved from Kwaśnicki (abstract checked, full-text definition not re-read) and analyticity |
| Theorem 14, Corollary 15 (bulk, one sign change) | proved under (EQ), given Lemma 12 |
| **Theorem 1 (exact eventual count M_+ + M_− + 1 under (SPAN), (LR), (LD2), (EQ))** | **proved, modulo writing out Lemma 12** |
| Theorem 1′ (general indices, outside two windows) | proved (same proviso) |
| Bulk with θ_τ̄ → 0; the window of `thm:window` | open |

**Points a reader should check first.**
1. Lemma 8, step (1): the Fourier bound for truncated sums, and the exponent condition on δ.
2. The bad-index estimate in Theorem 10, the only place where (EQ) enters step (c).
3. Lemma 12.

**For F.** Theorem 1 replaces `conj:three-modes` under (LD2) and (EQ). The hypothesis (LD) of
§5.4 can then be replaced by (LD2), which implies it. The three named steps of
sec_shape.tex:920–925 correspond to Theorems 7, 10 and 14. The cost estimate in the plan (10–12
pages) looks right. Lemma 8 and Lemma 12 are the long pieces.

## Files added in this round

- `04_predictions.md`.
- `exact04.py`: the exact recursion and the brute-force check (`py -I exact04.py`).
- `check04_renewal_bigjump.py` (R1, R7), `check04_layer2.py` (R2), `check04_full.py` (R3–R6).
