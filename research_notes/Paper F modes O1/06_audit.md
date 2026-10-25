# Paper F, (O1): audit of Theorem 1 (exact eventual mode count) and its proof

Date: 2026-10-25. Audited: `04_report.md` §§1–5, `05_report.md` §§1–3, against `paperF/sec_setting.tex`,
`sec_shape.tex` (§5.4), `sec_bulk.tex`, `sec_appendix.tex`, `sec_bigjump.tex` (`lem:truncated`). Verdict and
confidence language in 04/05 was ignored. The numerics use a new engine, written from scratch for this audit,
kept outside the repository (scratch folder `audit06/`: `eng.py`, `brute.py`, `runs2.py`, `more.py`, `iff.py`);
none of the 04/05 scripts was run.

## 1. Claim cards

**Theorem 1 (04 §1, with 05).**
- Hypotheses: (SPAN), (LR), (LD2) for both signs; (EQ) c ≤ T_+/T_− ≤ C (so α_+ = α_− = α); fresh start of
  either sign or fair start; no ties κ̃_±(j+1) ≠ κ̃_±(j) for j < J_±, with u_∓ strictly decreasing on [J_±, ∞).
- Conclusion, for all large N (no uniformity in N claimed): the sign of D_N(j) = P_N(N−j−1) − P_N(N−j) is
  (i) that of Δκ̃_+ on j < J_+; (ii) negative on [J_+, (x_*−η')Λ_N]; (iii) D_N strictly increasing on the window;
  (iv) positive on [(x_*+η')Λ_N, (1−p)N − K_0B_N]; (v) ΔP_N changes sign once on |x_{N,k}| ≤ R = (1−p)K_0 + 1,
  strictly decreasing near the change. Mirror at the minus end. Hence exactly M_+ + M_− + 1 modes; and
  "exactly three modes iff each κ̃_± has one local maximum, which for a fresh or fair start holds iff u_∓ is
  nonincreasing on j ≥ 1".

**Lemma 8 (difference form of the local big jump).** (LR), (LD2) for the plus sign. For every ε there is K such
that for all m ≥ 1 and all n with L = n − mμ ≥ Ka(m): ∇V_m(n) = m(α+1)f(L)/L·(1 + θε), V_m(n) ≤ Cmf(L),
δV_m(n) = [f(L) + μ(α+1)mf(L)/L](1 + θε), q_{m+2}(n) − q_{m+1}(n) = [2μf(L) + μ²(α+1)mf(L)/L](1 + θε), and
q_{m+1}(n) ≤ C(T(L) + mf(L)). No upper restriction on m.

**Lemma 12c (second differences).** (LR), (LD2). |∇²u_m(n)| ≤ Cmf(L)/L² for all m ≥ 1 and L ≥ max(K_1a(m), L_0).

## 2. Independent derivations of the critical steps

- **Difference big jump.** With one giant summand, ∇V_m(n) ≈ m·E∇f(n − S_{m−1}) ≈ m∇f(L), and (LR)+(LD2) give
  ∇f(y) ~ (α+1)f(y)/y (I re-derived Lemma 2: the second-difference bound makes nΔf(n)/f(n) nearly constant on
  [n, λn], and regular variation of f fixes the constant at −(α+1)). The no-giant part is
  ≤ sup|∇f_w^{*m'}|·P(truncated deviation) ≤ Ca(m)^{−2}·(mT(δL))^{1/(5δ)} after one summation by parts; against
  the target mf(L)/L ≍ a(m)^{−2}r^{−α−2} (r = L/a(m)) the ratio is r^{α+2+ε}(r^{−α+ε})^{1/(5δ)} → 0, uniformly in
  m. The exponent 1/(5δ) is within `lem:truncated` (exponent z/(2w) ≈ 1/(4δ)). (D2) and (D3) follow by
  inserting one more run and splitting x ≤ ε_1L / x > ε_1L; the leading constants check:
  V_{m+1}(n) − V_m(n) ≈ (m+1)f(L−μ) − mf(L) = f(L) + μ(α+1)mf(L)/L + o(·).
- **Second differences of u.** d_n = Δu ~ −T(n)/μ² gives ∇d_n ~ f(n)/μ², i.e. Δ²u(j) ~ f_−(j)/μ_−², and in the
  algebra of Lemma 3 χ'_t = −α, χ'_d = α ê(1)²/(1+ĝ(1))² = α/μ². Agrees with Lemma 3. Also
  ∇²(u∗u) = d∗d and u∗u = v + u give Δ²v = O(T_−(j)).
- **Bell shape.** Kwaśnicki, arXiv:1710.11023v3 (27 Nov 2018), read in full text: the sign-change definition
  (maximal alternating sequence of length n+1), Definition 2.1 (strictly bell-shaped: f^{(n)} → 0 at ±∞ and
  changes sign exactly n times), Theorem 1.1 ("f is weakly bell-shaped. If in addition f is smooth, then f is
  bell-shaped") and Corollary 1.3 ("All stable distributions on R have bell-shaped density functions"), with no
  restriction on index or skewness. The text also notes that a differentiable f with f' ≠ 0 at its zeros has n
  sign changes iff it has n zeros. So the input is as stated in 05 §2. My own version of Lemma 16: for analytic
  g = f^{(n)}, the gaps between zeros, the two unbounded intervals and the even-order zeros each force a sign
  change of g', so the count n + 1 for g' rules out even-order zeros, and then also zeros of order ≥ 3. Hence
  h' ≠ 0 off the mode and h''(x_θ) < 0. Finiteness of the zero set, which 05 assumes silently, follows from the
  same count. Stable densities with α > 1 are entire, so analyticity holds.

## 3. Item-by-item verdicts

| Item | Verdict |
|---|---|
| Lemma 2 ((LR)+(LD2) ⇒ (LD), (LR2)) | proved as written |
| Lemma 3 (Δ²u ~ f_−/μ_−², Δ²v = O(T_−)) | proved as written. The split formula for ∇(a∗b)_n has an index slip at the cut (second sum should end at n−M−2), harmless: the boundary terms are O(t_{n/2}²) either way |
| Lemma 4 (plus runs, second order, m ≤ n^{1−η}) | proved, one wording repair: in (v), apply the proof of (ii) to h_i at level n−w **with threshold w itself** (not ⌈(n−w)/K_0⌉ < w), so truncated variables are never giants; adjust K_0 accordingly |
| Theorem 5, Corollary 6, Theorem 7 (step (b), no (EQ)) | proved as written. I checked A1–A6, including the two summations by parts in A1 and W_i = u_{i+1}∗ṽ; the error O(f_+(N)(T_−(j) + 1/N)) is beaten by T_+(N)f_−(j) on [J_0, KΛ_N] because N/j → ∞ and N²f_−(KΛ_N) ≍ K^{−α−1}N/Λ_N → ∞ |
| Lemma 8 (D0–D3) | proved as written; the boundary term of the split in step (1) is only asserted to be smaller, which is routine (one more halving gives (C/a)·P(half deviates)) |
| Theorem 10 (big-jump zone) | proved. Leading constants check: f(L)(2μ_+/μ_−² + 2/μ_−) = 2sf/μ_−² and (α+1)i_0(f/L)(μ_+ + μ_−)²/μ_−². (EQ) enters only in the bad indices m > i_0 + L/(2μ_+), which need j ≥ εN, through a_+(m) ≍ a_−(m) ≍ a(j). The q-kernel bound q^−_m(j) ≤ μ·sup_{r<j}u^−_{m−1}(r) supplies the 1/a factor used there. Note: the proof uses only L ≥ KB_N, i.e. j ≤ (1−p)(N − KB_N), which is a wider range than the stated j ≤ (1−p)N − KB_N |
| Lemma 11 (Fourier LLT for Δ^r of kernels) | proved as written |
| Lemma 12a (pointwise bound, ‖Δu_m‖_1 ≤ C/a) | proved as written; I re-derived the exact summations by parts in (R3) |
| **Lemma 12c** | **incomplete as stated.** In the no-giant part the bound Σ_{dev}\|∇g\| ≤ 2P(dev) loses a factor a(m): the bad term is Ca(m)^{−2}(mT(δL))^{1/(5δ)}, the target is mf(L)/L² ≍ a(m)^{−3}r^{−α−3}, and the ratio is r^{3+α+ε−(α−ε)/(5δ)}·a(m), unbounded for m ≍ N at fixed r = L/a(m) ≥ K_1 (the "using a(m) ≤ L" step runs the wrong way). Also, "a truncated variable is never a giant at threshold w' < w" is false as worded; use threshold w. **Correct after the restriction L ≥ μm** (more generally mT(L) ≤ L^{−κ}): then (mT(δL))^{1/(5δ)} ≤ L^{−(α−1−ε)/(5δ)} beats L^{−α−3−ε} for small δ. Every use of 12c in Lemma 12 satisfies L ≥ j/2 and m ≤ j/(2μ), or m < m_ε at level ≍ N, so this restriction costs nothing. Without it, the uniform statement would need the three-block summation by parts of Lemma 12a applied to the truncated sums |
| Lemma 12 ((T2), (T1), (T1w)) | proved, given 12c in the restricted form. I checked range (i) (T(j)a(j) → 0, T(j)a(j)²/j → 0), range (ii) (CK^{1−α+δ}A^{−r}), the summation by parts for q-shifts v > j/2, and the weighted tail (T1w): exponents 1−2α−1/α < −2/α and −2α−1/α < −3/α for α > 1, and the mixed term NT f² = T²/N = o(B_N^{−3}). The correction of 04's unweighted (T1) is right, and Theorem 14 uses only the weighted form |
| Lemma 13 / Lemma 16 (h'' < 0 at the mode, h' ≠ 0 elsewhere) | proved; the finiteness of the zero set should be stated (it follows from the same count). Uniformity over the compact Θ_EQ is correct |
| Theorem 14, Corollary 15 (bulk) | proved under (EQ). The identification ∫∂_2Φ(ζ(y),y)dy = −ζ'∫∂_1Φ, ζ' = μ_τθ_τ̄/μ_τ̄, turns ς_τ∂_1 + (ς_τ̄/θ_τ̄)∂_2 into ς_τ s/μ_τ̄ ∂_1 = d/dx, also for r = 2 |
| Junctions (04 §5.3) | **correct after one repair.** As stated, (iv) covers x_{N,k} ≥ K_0 (j ≤ (1−p)N − K_0B_N) while (v) covers \|x\| ≤ (1−p)K_0 + 1, leaving ((1−p)K_0 + 1, K_0) uncovered once pK_0 > 1. Repair: take R = K_0 + 1 in (v) (Theorem 14 holds for every R), or state (iv) as L ≥ K_0B_N, which is what the proof of Theorem 10 gives. The other junctions (copies/layer, layer/window with η'/2, window ⊂ [J_0, (x_*+1)Λ_N], layer/zone at N^{1−η} with the same η < 1 − 1/α) are correct. The order K_0, then R, then N is right, and "eventual" is quantified correctly: constants depend only on the laws, and there is no uniform N_0 for a class of laws |
| Where (EQ) is used | as stated: the bad indices of Theorem 10, θ_τ̄ ≥ θ_min and b_τ̄ ≍ B_N in Theorem 14 and (T2), and compactness in Lemma 13(d). Steps (b), the copies and the layer do not use it |
| Theorem 1, count M_+ + M_− + 1 | **correct after the junction repair** |
| Theorem 1, "three modes iff u_∓ nonincreasing on j ≥ 1 for a fresh or fair start" | **refuted** (necessity). At an end whose profile starts below u(1) (fair start with u(1) > 1/2, or the end of the opposite sign under a fresh start, κ̃(0) = 0), κ̃ has one local maximum whenever u is unimodal on j ≥ 1. Counterexample in §4. Correct form: three modes iff each κ̃_± has one local maximum; u_∓ nonincreasing on j ≥ 1 is sufficient for fresh and fair starts, and it is necessary only at an end with κ̃(0) = 1 |
| Corollary 17 (along N with min θ_{σ,N} ≥ θ_0, α_+ = α_−) | correct as stated, given Theorem 1. Equal indices make a_+/a_− slowly varying, so comparability at N/s transfers to all m ∈ [εN, N] by uniform convergence |
| Theorem 1′ (no (EQ)) | incomplete. The bad-index estimate on L ≥ Kλ_NB_N (e^{−cL/a_−(j)} against (a_−/a_+)²) is asserted in one sentence (end of 04 §4.2), not derived. Not needed for Theorem 1 |

## 4. Numerical checks (new engine)

- **Engine.** R_±[j,k] = P(a ± run starts after k plus and j minus steps), computed row by row in j (minus
  convolution by a direct sum, plus convolution by FFT). P_N(k) = Σ_x R_+[N−k, k−x]T_+(x) + Σ_y R_−[N−k−y, k]T_−(y).
  It agrees with a brute-force chain over (count, sign, age) to 1.2·10⁻¹⁶ at N = 3, 7, 15, 30 for both starts
  (plus zeta 3/2 with n ≥ 2, minus zeta 1.2). At N = 2500 the smallest relative gap |D_N(j)|/P_N(N−j), j < 200,
  is 3.9·10⁻⁵, far above the rounding error.
- **Runs ≥ 2** (f(n) ∝ n^{−5/2} on n ≥ 2, both signs, fair start). κ̃ = (½, u(1), …) has M = 7 local maxima, at
  j = 0, 2, …, 12; Δ²u ≤ 0 exactly at j = 2, 4, …, 18, so J_0 = 19. Prediction M_+ + M_− + 1 = 15. Mode counts at
  N = 1000, 1500, …, 4000: 17, 19, 17, 15, 15, 15, 15. At every N = 2500, 2600, …, 4000 the count is 15. The
  plus-end modes are at j = 0, 2, …, 12 from N = 2500; below that there are extra maxima at j = 14 (and 16).
  This agrees with 04 R6 and with an eventual, non-uniform statement.
- **Log-convex** (zeta 3/2, both signs). Exactly 3 modes, for the fresh plus and the fair start, at
  N = 200, 500, 1000, 2000, 3000, 4000: modes at k = 1, N/2 and N (fresh plus) or N−1 (fair).
- **Counterexample to the "iff" clause.** f(1) = 0.6, f(2) = 0.3, f(n) ∝ n^{−5/2} on n ≥ 3 with mass 0.1, both
  signs. It satisfies (SPAN), (LR) and (LD2). Here u = 0.6, 0.66, 0.615, 0.609, …, strictly decreasing from
  j = 2, so u is not nonincreasing on j ≥ 1. For the fair start, κ̃_± = (½, 0.6, 0.66, …) has one local maximum,
  and P_N has exactly 3 modes (k = 2, N/2, N−2) at N = 1000, 1500, 2000 (5 at N = 500). For the fresh plus start,
  M_+ = 2 and M_− = 1, and P_N has 4 modes, as the count M_+ + M_− + 1 predicts.

## 5. Bottom line

Theorem 1's count M_+ + M_− + 1 holds, under (SPAN), (LR), (LD2), (EQ), for fresh or fair starts with no ties,
after three local repairs:
1. Lemma 12c restricted to L ≥ μm, which covers all its uses.
2. The (iv)/(v) overlap fixed by R = K_0 + 1.
3. The truncated-giant threshold in Lemma 4(v) and Lemma 12c set to w.

The "iff u_∓ nonincreasing" clause must be weakened to the κ̃ criterion. Lemma 8 and Theorem 10 are proved as
written, and the bell-shape input is as cited.
