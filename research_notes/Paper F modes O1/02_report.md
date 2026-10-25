# Paper F, (O1), second round: M1 proved, the fallback theorem, and what remains

Date: 2026-10-25. This round continues `01_report.md`, which is left unchanged.
Predictions were written in `02_predictions.md` before the runs. The scripts are run with
`py -I` from this folder.

## 0. Summary

1. **Lemma 1 now has a self-contained proof** (§1). The proof uses only Wiener's lemma, with a
   truncation and a Neumann series. The citation to Chover–Ney–Wainger is no longer needed.
   - I could not check its theorem number: the paper (J. Analyse Math. 26 (1973) 255–302) is
     paywalled, and the open copies I found give only the bibliographic data. This is no
     longer a dependency.
2. **M1 is proved** (§2–§3) under the following hypotheses:
   - (RV) and (SPAN) for the minus sign;
   - (LR) for the plus sign;
   - **(LR2-O)** f_+(n) − f_+(n+1) = O(f_+(n)/n).
   - (LR2-O) is weaker than the asymptotic smooth-tail hypothesis proposed by the coordinator.
     The proof covers fresh plus, fresh minus and fair starts, uniformly in 1 ≤ j ≤ N^{1−η}.
   - It uses only F's own lemmas, so no external local limit theorem for differences is needed.
   - Numerically the error is about 30·j/N for all three starts (Q1, Q2 confirmed).
3. **The fallback theorem, fully proved** (§4). Under (RV),(SPAN),(LR),(LR2-O) for both signs,
   for all large N:
   - within distance N^{1−η} of each end, the extrema of P_N are exactly those of the end
     profile κ̃;
   - they are followed by an odd number of extrema, all at distance x_*Λ_N(1+o(1)) from that
     end (the antimode cluster, which contains Theorem E's j*_N);
   - P_N is then strictly monotone up to distance N^{1−η}.
   - Together with the lower bound (Theorem 4 of 01), this gives the exact number of local
     maxima near the ends outside two windows of width o(Λ_N).
4. **M2 (exactly one antimode), M3 (the big-jump zone) and M4 (the bulk) remain open** (§5).
   The report gives the exact estimates each one needs.
   - For M4, the bell shape of stable densities (Kwaśnicki, Trans. AMS 373 (2020)) gives
     h' ≠ 0 away from the mode and h'' < 0 at the mode, by a short argument (§5).
5. **Every N** (§6). The claim "at most three local maxima for every N for completely
   monotone laws" is **false for a fresh plus start**: a mixture of two geometric laws has four
   local maxima at N = 186.
   - The claim is not refuted for fair starts, or with regularly varying tails.
   - Total positivity faces a structural obstacle: completely monotone kernels are reverse-rule,
     not Pólya frequency.

## 1. Lemma 1, self-contained

**Lemma 1.** Assume (RV) and (SPAN) for the minus sign. Write t_n = T_−(n+1) and
d_n = u_−(n) − u_−(n−1), with u_−(−1) = 0. Then d ∈ ℓ¹ and d_n = −(1+o(1)) t_n/μ_−².

*Proof.*

**Setting up.**
- Put T̂(z) = Σ_{n≥0} t_n zⁿ. Then (1−z)T̂ = 1 − F_−, so D(z) := Σ d_n zⁿ = 1/T̂(z).
- On |z| ≤ 1, T̂ ≠ 0. A zero would force F_−(z) = 1 with z ≠ 1, which (SPAN) excludes, and
  T̂(1) = μ := μ_− ≠ 0.
- Wiener's lemma for ℓ¹(ℤ_{≥0}) then gives d ∈ ℓ¹.

**The weighted norm.**
- t is nonincreasing and regularly varying with index −α_−, so c_t := sup_n t_{⌊n/2⌋}/t_n is
  finite.
- For sequences on ℤ_{≥0}, put ‖a‖_t = sup_n |a_n|/t_n. Splitting the convolution at n/2 gives
  (W) ‖a∗b‖_t ≤ c_t(‖a‖_1‖b‖_t + ‖a‖_t‖b‖_1).

**Product rule.** If a, b ∈ ℓ¹ with a_n/t_n → χ_a and b_n/t_n → χ_b, then
(a∗b)_n/t_n → â(1)χ_b + b̂(1)χ_a.
- In Σ_{k≤n/2} a_k b_{n−k}/t_n, each term converges, since t_{n−k}/t_n → 1 for fixed k.
- The terms are dominated by c_t‖b‖_t|a_k|, so dominated convergence applies.
- The other half of the sum is the same.

**Truncation.**
- Split t = t' + t'' with t'_n = t_n 1{n ≤ M}.
- Choose M so large that ‖d‖_1‖t''‖_1 ≤ 1/2 and c_t·2‖d‖_1‖t''‖_1 ≤ 1/4.
- Then T̂' = T̂(1 − T̂''D) has no zeros on |z| ≤ 1.
- So E := 1/T̂' has coefficients e = d ∗ Σ_k (−d∗t'')^{∗k}, with ‖e‖_1 ≤ 2‖d‖_1.
- T̂' is a polynomial with no zeros in the closed disk, so e decays geometrically and
  e_n = o(t_n).

**Neumann series.**
- Put g = e∗t''. Then g_n/t_n → ê(1) =: χ_g by the product rule, since t''_n = t_n for n > M,
  and ‖g‖_1 ≤ 1/4.
- By (W), x_k := ‖g^{∗k}‖_t ≤ c_t‖g‖_1 x_{k−1} + c_t‖g‖_t‖g‖_1^{k−1}. So x_k ≤ Ck4^{−k}, which
  is summable.
- By induction with the product rule, (g^{∗k})_n/t_n → k ĝ(1)^{k−1}χ_g.
- By dominated convergence over k, h := Σ_{k≥1}(−g)^{∗k} satisfies
  h_n/t_n → −χ_g/(1+ĝ(1))².

**Conclusion.**
- D = E·(1 + ĥ), so d = e + e∗h and d_n/t_n → ê(1)χ_h.
- Here ê(1) = 1/T̂'(1), χ_g = 1/T̂'(1), and 1 + ĝ(1) = T̂(1)/T̂'(1) = μ/T̂'(1).
- So d_n/t_n → −(1/T̂'(1))²·(T̂'(1)/μ)² = −1/μ². ∎

**Lemma 2 of 01** (the prepared kernel) now rests on the same product rule.

## 2. Plus-side lemmas

Write f = f_+, T = T_+, μ = μ_+, α = α_+, S_m = S^+_m, V_m(n) = f^{∗m}(n) (V_0 = δ_0),
δV_m = V_{m+1} − V_m, and q_m = q^+_m (so q_1 = T). Assume (RV),(LR),(LR2-O) for the plus sign
and fix η ∈ (0,1). "Uniformly" means over 0 ≤ m ≤ n^{1−η}, as n → ∞.

The facts used from F are:
- `lem:local-bigjump`: V_m(n) = m f(n)(1+o(1)) uniformly in 1 ≤ m ≤ n^{1−η};
- `lem:truncated`;
- `lem:sums`;
- `lem:rv`: f(n') ≤ C f(n) for n' ≥ n/8, and f(n−a)/f(n) → 1 for a = o(n).

**(P0)** q_{m+1}(n) ≤ C T(n), uniformly.
- *Proof.* q_{m+1}(n) = Σ_{x<n} V_m(x)T(n−x).
- The part x ≤ n/2 is at most T(n/2) ≤ CT(n).
- The part x > n/2 is at most sup_{x>n/2}V_m(x)·Σ_l T(l) ≤ Cmf(n)μ ≤ CT(n), using (LR) and
  m ≤ n. ∎

**(P3)** |V_m(n−1) − V_m(n)| ≤ C m f(n)/n, uniformly in 1 ≤ m ≤ n^{1−η}.
- *Proof.* Fix K_0 > 4(α+3)/(α−1) and put w = ⌈n/K_0⌉.
- **No summand ≥ w.** `lem:truncated` with z = n − mμ ≥ n/2 bounds the event by
  C(mT(w))^{K_0/4} ≤ C n^{−(α−1+η/2)K_0/4} = o(f(n)/n). The same bound holds at n−1.
- **Some summand ≥ w.** Let I be the first index with X_I ≥ w, and put
  h_i(z) = P(X_l < w for l < i, Σ_{l≠i}X_l = z). Then P(S_m = n, I = i) = Σ_{y≥w} f(y)h_i(n−y).
- Its n-difference is
  Σ_{z≤n−1−w} h_i(z)[f(n−1−z) − f(n−z)] − h_i(n−w)f(w).
- In the first part, (LR2-O) and y ≥ n/K_0 give |f(y) − f(y+1)| ≤ C f(n)/n, and
  Σ_z h_i(z) ≤ 1.
- In the second part, h_i(n−w) ≤ V_{m−1}(n−w) ≤ Cmf(n), so the term is at most
  Cmf(n)² = o(f(n)/n), since mnf(n) ≤ CmT(n) → 0.
- Summing over i ≤ m gives the claim. ∎

**(P1)** δV_m(n) = f(n)(1+o(1)), uniformly.
- *Proof.* δV_m(n) = Σ_{x≥1} f(x)[V_m(n−x) − V_m(n)].
- **x ≤ n/2.** By (P3) at arguments ≥ n/2, |V_m(n−x) − V_m(n)| ≤ Cmxf(n)/n. The total is at
  most Cμ m f(n)/n = o(f(n)).
- **x > n/2.** This part is Σ_{1≤y<n/2} f(n−y)V_m(y) − V_m(n)Σ_{x>n/2}f(x).
  - The second term is at most Cmf(n)T(n) = o(f(n)).
  - In the first, f(n−y)/f(n) is bounded and tends to 1 for y = o(n).
  - Moreover P(S_m < n/2) → 1 and P(S_m > εn) ≤ mμ/(εn) → 0.
  - So the first term is f(n)(1+o(1)).
- For m = 0, δV_0(n) = f(n) exactly. ∎

**(P2)** q_{m+2}(n) − q_{m+1}(n) = 2μ f(n)(1+o(1)), uniformly in 0 ≤ m ≤ n^{1−η}.
- *Proof.* Two identities are used:
  - q_{m+2}(n) = Σ_x f(x)q_{m+1}(n−x), with q(k) = 0 for k ≤ 0 (put one extra run in front);
  - q_{m+1}(l−1) − q_{m+1}(l) = δV_m(l−1).
- So the difference is Σ_x f(x)[q_{m+1}(n−x) − q_{m+1}(n)].
- **x ≤ n/2.** The bracket is Σ_{i=1}^{x} δV_m(n−i) = x f(n)(1+o(1)) by (P1), dominated by
  Cxf(n). Since Σ x f(x) = μ, this part is μf(n)(1+o(1)).
- **x > n/2.** This part is Σ_{1≤y<n/2} f(n−y)q_{m+1}(y) − q_{m+1}(n)T(⌈n/2⌉+…).
  - The second term is O(T(n)²) = o(f(n)) by (P0).
  - In the first, Σ_y q_{m+1}(y) = E X_{m+1} = μ.
  - Also Σ_{y≥εn} q_{m+1}(y) ≤ E[X;X ≥ εn/2] + μP(S_m ≥ εn/2) → 0 uniformly.
  - So the first term is μf(n)(1+o(1)). ∎
- In particular (m = 0), q_2(n) = T(n) + 2μf(n)(1+o(1)).

**(P5)** T(N−a) = T(N) + af(N)(1+o(1)) and f(N−a) = f(N)(1+o(1)), uniformly in
a ≤ 2N^{1−η}. This follows from (LR) and `lem:rv`(i).

## 3. Theorem M1 (first differences in the layer)

**Theorem M1.** Assume (RV),(SPAN) for the minus sign and (LR),(LR2-O) for the plus sign. Fix
η ∈ (0,1). Take a fresh start of either sign, or a mixture with weights w_+ + w_− = 1. Put
R_N(j) = P_N(N−j)/T_+(N), u = u_−, v = v_−, Δx(j) = x(j+1) − x(j), and

Ψ(j) = α_+[(j+1)Δu(j) + 2μ_+Δv(j) + 2u(j) − 2μ_+ w_− Δu(j)].

Then, uniformly in 1 ≤ j ≤ N^{1−η},
N(R_N(j+1) − R_N(j)) = NΔu(j) + Ψ(j) + o(1).

For a fresh plus start Ψ = ΔC, with C of `eq:Cj`.

*Proof.* By linearity it suffices to treat the two fresh starts. Let j ≥ 1 and n = N − j.

**The identity.** `prop:fresh-identity` and its minus form give
P_N(N−j) = Σ_{m≥1}[a_m(j)Q_m(n) + V_m(n)b_m(j)], with a_m(j) = u^−_m(j) and V_m = u^+_m.
- Plus start: Q_m = q^+_{m+1} and b_m = q^−_m.
- Minus start: Q_m = q^+_m and b_m = q^−_{m+1}.

**The split.** Differencing gives T_+(N)·(R_N(j+1) − R_N(j)) = I + II + III + IV, where
- I = Σ_m Δa_m(j)Q_m(n−1);
- II = Σ_m a_m(j)[Q_m(n−1) − Q_m(n)];
- III = Σ_m V_m(n−1)Δb_m(j);
- IV = Σ_m[V_m(n−1) − V_m(n)]b_m(j).

Only m ≤ j+1 occurs, since u^−_m(i) = 0 and q^−_m(i) = 0 for m > i.

**Minus-side facts** (exact, except where stated).
1. Σ_m a_m(j) = u(j) and Σ_m m a_m(j) = v(j).
2. Write Ā_i(j) = Σ_{m>i}a_m(j) = Σ_{x<j}u^−_i(x)u(j−x). Then
   Σ_{i≥1}|Ā_i(j+1) − Ā_i(j)| ≤ 1 + ‖Δu‖_1 =: V_u, which is finite by Lemma 1.
3. (j+1)|Δu(j)| ≤ C, by Lemma 1 and jT_−(j) → 0.
4. Δ(v+u)(j) = [z^j]U·D, so |Δv| ≤ 1 + ‖d‖_1.
5. Write B̄_i(j) = Σ_{m>i}b_m(j). It equals P(S^−_i < j) for the plus start and
   P(S^−_{i+1} < j) for the minus start. So B̄_i(j+1) − B̄_i(j) = u^−_i(j), respectively
   u^−_{i+1}(j). Also Σ_m Δb_m(j) is 0, respectively f_−(j).
6. Σ_m m b_m(j) ≤ j+2.

**II.** Q_m(n−1) − Q_m(n) = δV_m(n−1) for the plus start and δV_{m−1}(n−1) for the minus
start. By (P1) and (P5), II = f_+(N)u(j) + o(f_+(N)).

**III.**
- Write V_m = V_1 + Σ_{i<m}δV_i and sum by parts with fact 5.
- Plus start: III = Σ_{i≥1}δV_i(n−1)u^−_i(j) = f_+(N)u(j) + o(f_+(N)).
- Minus start: III = V_1(n−1)f_−(j) + Σ_{i≥1}δV_i(n−1)u^−_{i+1}(j)
  = f_+(N)[f_−(j) + u(j) − u^−_1(j)] + o(f_+(N)) = f_+(N)u(j) + o(f_+(N)).

**IV.** By (P3), |IV| ≤ C(f_+(N)/N)Σ_m(m+1)b_m(j) ≤ Cf_+(N)(j+3)/N = o(f_+(N)).

**I.**
- Write Q_m = Q_1 + Σ_{i<m}δ_i with δ_i = Q_{i+1} − Q_i. Then
  I = Q_1(n−1)Δu(j) + Σ_{i≥1}δ_i(n−1)[Ā_i(j+1) − Ā_i(j)].
- By (P2), δ_i = 2μ_+f_+(N)(1+o(1)). Fact 2 and Σ_{i≥1}[Ā_i(j+1) − Ā_i(j)] = Δv − Δu give
  for the second sum 2μ_+f_+(N)(Δv − Δu) + o(f_+(N)).
- For Q_1(n−1):
  - plus start: Q_1(n−1) = q_2(N−j−1) = T_+(N) + (j+1+2μ_+)f_+(N) + o((j+1)f_+(N));
  - minus start: Q_1(n−1) = T_+(N−j−1) = T_+(N) + (j+1)f_+(N) + o((j+1)f_+(N)).
- By fact 3 the o-terms times Δu(j) are o(f_+(N)).

**Sum.**
- Adding the four parts:
  T_+(N)ΔR_N = T_+(N)Δu + f_+(N)[(j+1)Δu + 2μ_+Δv + 2u − 2μ_+ 1_{minus}Δu] + o(f_+(N)).
- The bracket is bounded uniformly in j by facts 3 and 4.
- Multiplying by N/T_+(N) and using Nf_+(N)/T_+(N) → α_+ gives the claim. ∎

**Remarks.**
- Ψ(j) → c_a = 2α_+s/μ_−² as j → ∞. Indeed (j+1)Δu → 0, Δu → 0, u → 1/μ_−, and
  Δv → 1/μ_−² because (u∗d)_j → (1/μ_−)·d̂(1) by dominated convergence.
- The proof does not use (LR) or (LR2-O) for the minus sign.
- **Numerics** (`py -I check_M1_starts.py`): the discrepancy
  N·ΔR_N − NΔu − Ψ is about 30–34·j/N for the plus, minus and fair starts. For example, at
  j = 20 it is 0.066, 0.063 and 0.065 at N = 10⁴. It shrinks like 1/N at fixed j. The
  discrepancy is O(j/N), which the theorem's o(1) contains.

## 4. Theorem F2: the fallback, fully proved

**Hypotheses.**
- (RV),(SPAN),(LR),(LR2-O) for both signs.
- A fresh start of either sign, or the fair start.
- At the plus end, the profile κ̃_+ is:
  - (1, u_−(1), u_−(2), …) for a plus start;
  - (0, u_−(1), …) for a minus start;
  - (½, u_−(1), …) for the fair start.
- No ties: u_−(j+1) ≠ u_−(j) for j ≥ 1, and κ̃_+(1) ≠ κ̃_+(0). The same at the minus end.
- By Lemma 1 there is J_+ with u_− strictly decreasing on [J_+, ∞).
- Put Λ_N = a_−(N) and x_*^{−α_−} = 2α_+s, as in `thm:antimode`. Fix η ∈ (0, 1 − 1/α_*) and
  η' > 0.

**Theorem F2.** For all large N, with D_N(j) = P_N(N−j−1) − P_N(N−j):
- (a) sign D_N(j) = sign(κ̃_+(j+1) − κ̃_+(j)) for 0 ≤ j < J_+;
- (b) D_N(j) < 0 for J_+ ≤ j ≤ (x_*−η')Λ_N;
- (c) D_N(j) > 0 for (x_*+η')Λ_N ≤ j ≤ N^{1−η};
- (d) D_N changes sign an odd number of times on the window between (b) and (c). The window
  contains Theorem E's j*_N.

The same holds at the minus end, with the signs exchanged, a_+(N) in place of Λ_N, and
x^{−α_+} = 2α_−s.

**Consequences.**
- For all large N, the local extrema of P_N within distance N^{1−η} of either end are:
  1. exactly the local extrema of κ̃_±, at the same positions;
  2. an odd number of extrema at distance x_*Λ_N(1+o(1)), the antimode cluster.
- The local maxima there, outside the two windows of width o(Λ_N), are exactly the M_± local
  maxima of κ̃_±.
- With the interior global mode (`thm:mode`(a)), P_N has at least M_+ + M_− + 1 local maxima.

*Proof.*
- **(a), and (b) on a fixed initial range.** On any fixed window this is Proposition 3 of 01,
  which uses `thm:bigjump`(a) or `thm:preparation`(d). It applies to j < J' for any fixed J',
  and Δu < 0 on [J_+, J').
- **(b) for J' ≤ j ≤ (x_*−η')Λ_N.**
  - By Theorem M1 and Lemma 1, N·D_N(j) = −NT_−(j)(1+o(1))/μ_−² + Ψ(j) + o(1). The o(1) in
    Lemma 1 is as j → ∞, so it is uniform for j ≥ J' once J' is large.
  - Since T_− is monotone, NT_−(j) ≥ NT_−((x_*−η')Λ_N) → (x_*−η')^{−α_−} > x_*^{−α_−} = c_aμ_−².
  - And Ψ(j) ≤ c_a + o_{J'}(1).
  - So N·D_N < 0 for J' large and then N large.
- **(c).** Symmetrically, NT_−(j) ≤ NT_−((x_*+η')Λ_N) → (x_*+η')^{−α_−} < c_aμ_−², and
  Ψ(j) ≥ c_a − o(1). M1 covers j ≤ N^{1−η}, and N^{1−η} ≥ KΛ_N for every K.
- **(d)** follows from (b) and (c). By `thm:antimode`(a), j*_N/Λ_N → x_*.
- **The minus end** is the same argument with the signs exchanged. This is where (LR) and
  (LR2-O) for the minus sign enter. ∎

**What this gives for the criterion.** The "only if" half was already proved. In the "if"
half, only two places remain open:
- (i) the inside of the two antimode windows (M2);
- (ii) the stretch from distance N^{1−η} to the bulk (M3, M4).

## 5. What remains

**(M2) One antimode.** The window has width o(Λ_N). It suffices to show that
NΛ_N(D_N(j+1) − D_N(j)) ≥ c > 0 there.

The main term is NΛ_NΔ²u(j). It needs Δd_n ~ f_−(n)/μ_−², a difference form of Lemma 1. That
requires a version of the §1 argument for the algebra
{a : sup|a_n|/t_n + sup|Δa_n|/f_n < ∞}, which I have not done.

The four parts of §3 must then be differenced once more. The tools needed, in order:
- (S1) second m-differences |δ²V_m(n)| ≤ Cf(n)/n;
- (S2) |Δ_nδV_m(n)| ≤ Cf(n)/n and |Δ_nδQ_m(n)| ≤ Cf(n)/n;
- (S3) for part I, summation by parts in i with Σ_i|Δ²_jΣ_{m>i}(m−i)a_m(j)| = O(1). This
  holds: the inner sum is E[v(j−S^−_i); S^−_i < j], and Δ²v ∈ ℓ¹ by the product rule;
- (S4) for part IV, a second n-difference of f^{∗m}.

Under (LR2-O) alone, (S4) fails at the needed precision o(f/Λ_N). The crude bound gives
O(jf/N), and Λ_N²/N → ∞. Two ways out:
- **(LR3)** |Δ²f(n)| ≤ Cf(n)/n² for the plus sign;
- **smoothing.** Move one difference onto f^{∗(m−1)} by summation by parts, using a TV bound
  Σ_y|f^{∗m}(y+1) − f^{∗m}(y)| ≤ C/a_+(m). This works because Λ²/(N a_+(Λ)) → 0: the
  exponent is −(1−1/α)² for equal indices. I did not locate an exact source for the TV bound
  in the stable domain.

Numerically, the second differences are positive on [1, 3j*) (P5 of 01). M2 looks provable
under (LR3), at the cost of several pages.

**(M3) The big-jump zone at the level of differences.** This covers N^{1−η} ≤ j ≤ (1−p)N − KB_N.
- The run index m reaches order N there, so `lem:local-bigjump` (m ≤ n^{1−η}) no longer
  applies.
- One needs a difference version of the giant-run decomposition of `lem:giant` and of
  `lem:one-giant`, to precision o(G_N/L_k).
- This is where (LR2) enters for the f_+ term of the kernel, smoothed over the weights χ_j.
  The first part of `rem:no-single-formula` must also be redone for differences.
- When θ_{+,N} → 0, the window that F does not describe sits inside M3, so M3 also needs O2.
- I did not check the difference statements of Berger (PTRF 2019) or Caravenna–Doney (EJP
  2019) against their texts. Both treat strong renewal or local deviations at the value level.
  Neither is used in this report.

**(M4) The bulk.** This needs a derivative local limit theorem uniformly on |x| ≤ K, with
second derivatives near the mode:
- B_N²ΔP_N(k) = h_N'(x_{N,k}) + o(1);
- B_N³Δ²P_N = h_N'' + o(1).

The shape input closes as follows.
- Stable densities are bell-shaped (Kwaśnicki, "A new class of bell-shaped functions",
  Trans. AMS 373 (2020); arXiv 1710.11023): h^{(n)} changes sign exactly n times.
- With analyticity this gives h' ≠ 0 off the mode and h''(mode) < 0:
  - an extra zero of h' would be a strict extremum of h', adding a sign change of h'';
  - h''(mode) = 0 would force at least five extrema of h'', so at least five sign changes of
    h''', against three.
- For equal indices every h_θ is stable. For unequal indices only the limit θ matters.
- Yamazato's unimodality alone does not give h' ≠ 0, as the coordinator noted. The bell shape
  is the needed source.
- The derivative local limit theorem itself is a difference version of the long proof of
  `thm:bulk`. It is not done.

## 6. Every N: a bounded look

`py -I check_cm_everyN.py` scans mixtures of geometric laws (completely monotone) and the zeta
law with α = 1.1, for every N ≤ 300.

- **Fair start:** at most 5 sign changes in every case.
- **Fresh plus start:** 6 sign changes, that is **four local maxima** (`py -I inspect_cm.py`).
  - Weights 0.9 and 0.1 on geometric laws with P(X>n) = 0.1^n and 0.99^n, at N = 186:
    local maxima at k = 3, 97, 184, 186.
  - Mixture 0.5/0.5 with parameters 0.3/0.97, at N = 131: local maxima at 4, 71, 129, 131.
  - These are not rounding effects: the relative differences are at least 5·10⁻⁵.
- So "at most three local maxima for every N for completely monotone laws" is false as stated.
  It could survive only for the fair start, or with regularly varying tails: no counterexample
  was found for zeta laws.

**The obstacle for total positivity.**
- A completely monotone law is log-convex. Its kernel is reverse-rule (RR₂), not a Pólya
  frequency kernel.
- Karlin's variation-diminishing property for the count needs Pólya frequency kernels, or a
  composition of kernels whose signs work out.
- The hidden-rate Markov chain (sign, θ, k) increases k by a 0/1 shift. I found no ordering of
  θ that makes its transition kernel TP₂ in (θ, k) jointly.
- I stopped here.

## 7. Status table

| Claim | Status |
|---|---|
| Lemma 1, Lemma 2 (01) | proved, self-contained modulo Wiener's lemma |
| (P0)–(P5), Theorem M1 (all fresh and fair starts) | proved |
| Theorem F2 (exact structure up to distance N^{1−η}, apart from the antimode cluster) | proved |
| Lower bound of at least M_+ + M_− + 1 modes (01, Theorem 4) | proved |
| M2 (one antimode) | open; reduced to (S1)–(S4); probably needs (LR3) or the smoothing route |
| M3, M4, and exactly three modes | open |
| At most three modes for every N, CM laws, fresh start | false (counterexample) |
| The same for the fair start, or zeta laws | open; no counterexample for N ≤ 300 |

## 8. Labels of F used

`prop:fresh-identity`, `eq:q-cover`, `eq:kernel-sums`, `eq:cover`, `eq:conv-v`, `eq:Cj`,
`lem:local-bigjump`, `lem:truncated`, `lem:sums`, `lem:rv`, `thm:bigjump`(a),
`thm:preparation`(d), `thm:second-order`, `thm:antimode`(a), `thm:mode`(a).

## Files added in this round

- `02_predictions.md`.
- `check_M1_starts.py` (about 12 s).
- `check_cm_everyN.py` (about 3 s) and `inspect_cm.py`.
- `engine.py` gained `layer_R_mixed`. Earlier functions are unchanged.

Sources consulted on the web: the bibliographic records of Chover–Ney–Wainger (the paper is
paywalled), and Kwaśnicki, arXiv 1710.11023 and 1910.07752 (abstracts only).
