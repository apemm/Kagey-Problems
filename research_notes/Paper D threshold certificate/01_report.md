# Paper D: certifying the unimodal to bimodal threshold of the fair-start limit

Date: 2026-10-25. Folder contents:

- `scripts/erw_cf.py` builds the ball-arithmetic enclosure of f_a''(0) (Lemmas 1 to 5 below).
- `scripts/certify_fpp.py` is the driver. It has three modes, `point`, `bisect` and `scan`.
- `scripts/check_moments.py` runs consistency checks of the moment input, in exact and ball arithmetic.
- `scripts/check_density_float.py` compares the Fourier density with the exact finite-n mass function. This is float evidence only.
- `data/*.txt` holds the stored outputs of the runs listed in Section 4.
- `sources/` holds text copies of GLR (arXiv:2308.14630v2), GLRS (arXiv:2409.06836) and Trinas-Valle (arXiv:2609.14753v1). They are data only, copied from `research_notes/Paper D independent JTP review/literature_erw/`.

Software: Python 3.14, python-flint 0.9.0 (arb), mpmath 1.3.0, numpy. Every run uses `py -I`.

## 1. Summary

- **Literature.** No source settles the number of modes of g_a = (f_a(x)+f_a(-x))/2.
  - GLRS (EJP 2025), Remark 2.1(b), states the conjecture: L_q is bimodal iff |q-1/2| < q(a), and calls it "believed to be challenging".
  - Trinas-Valle (Sept 2026, discussion of mixtures) only notes that unimodality does not pass to mixtures.
  - A web search on 2026-10-25 found nothing newer, so the search was not stopped by an existing proof.
- **Certified, at exact rational a.** All results are rigorous ball arithmetic with an analytic tail bound (Section 3). There is no float step.
  - f_a''(0) < 0 at a = 0.501, 0.505, 0.51, 0.52, ..., 0.665, 0.668.
  - f_a''(0) > 0 at a = 0.669, 0.67, ..., 0.96, 0.97.
  - The bisection gives

        f''(0) < 0 at a_1 = 0.66881286001455 = 13376257200291/2·10^13,
        f''(0) > 0 at a_2 = 0.6688128600146  = 3344064300073/5·10^12,

    with a_2 - a_1 = 5·10^-14. At a_1 the enclosure is f'' ∈ [-3.50e-14, -3.31e-14]. At a_2 it is f'' ∈ [4.1964e-16, 4.1966e-16].
  - Assume the companion theorem (g_a has at most two modes). Then at each of these points g_a is unimodal (sign -) or bimodal (sign +), because g_a''(0) = f_a''(0).
- **Not proved.** The sign on whole intervals of a. The certificate is pointwise, and nothing here controls f_a''(0) between grid points. The two ends a ↓ 1/2 and a ↑ 1 are also open (Section 6).
- **Numerical estimate.** a_c ≈ 0.66881286001460, consistent with the supplied interval [0.6688128591, 0.6688128614]. If a ↦ f_a''(0) is continuous, a zero lies in (a_1, a_2). Continuity is very plausible but is not proved here.

## 2. Inputs from the literature (checked in `sources/`)

- **(F) Fixed point.** GLR Thm 1.1: L = V^a L' + (2ξ_p - 1)(1-V)^a L'', with V ~ U[0,1], ξ_p ~ Bernoulli(p), all independent and L', L'' ~ L. Conditioning on V gives GLR (2.10):

      φ(t) = p E[φ(tV^a) φ(t(1-V)^a)] + (1-p) E[φ(tV^a) φ(-t(1-V)^a)].

  Since |φ(-s)| = |φ(s)|, this gives, for all real t,

      |φ(t)| ≤ ∫_0^1 |φ(tv^a)| |φ(t(1-v)^a)| dv.        (2.1)

- **(M) Moments.** GLR Thm 1.4 and GLRS (3), (12): E[L^n] = n! m_n / Γ(1+an), with m_0 = m_1 = 1 and

      m_n = (na - c_n)^-1 Σ_{j=1}^{n-1} c_j m_j m_{n-j},   c_j = 1 (j even), a (j odd).

  The two papers write the same formula: GLR has (k-1)! m_k/(aΓ(ka)) = k! m_k/Γ(1+ka). `check_moments.py` checks the following.
  - m_2 = a/(2a-1) and m_3 = (a+1)/(2(2a-1)), the coefficients of GLRS (4), in exact rationals.
  - E L = 1/Γ(1+a) and E L^2 = 1/((2a-1)Γ(2a)), which agree with Bercu and GLR Thm 2.1, in balls.
- **(S) Analyticity.** GLR Cor 2.11: E e^{tL} < ∞ for all real t. So E e^{|t||L|} < ∞, and φ(t) = Σ_n m_n (it)^n / Γ(1+an) for every real t.
- **(D) Density.** GLR Thm 1.3: L has a continuous density f = f_a.

## 3. What is proved (the certificate's mathematics)

Throughout, a ∈ (1/2, 1) is a fixed rational. Write c_n = m_n/Γ(1+an) and let P_N be the partial sum up to degree N.

**Lemma 1 (moment bound).** Fix N ≥ 2 and put A = ((N+1)a - 1)/N. Suppose B satisfies m_j ≤ A B^j for 1 ≤ j ≤ N. Then m_n ≤ A B^n for all n ≥ 1.

*Proof.* Use induction on n > N. Each c_j ≤ 1, and na - c_n ≥ na - 1 > 0. So

    m_n ≤ (n-1) A^2 B^n / (na-1).

Next, (na-1)/(n-1) increases in n, because its derivative is (1-a)/(n-1)^2. Hence A ≤ (na-1)/(n-1) for n ≥ N+1, which gives m_n ≤ A B^n. ∎

In the code, B is the upper end of max_j (m_j/A)^{1/j}, enlarged by a factor 1+2^-30. The inequality m_j ≤ A B^j is then re-checked in balls for every j ≤ N.

**Lemma 2 (truncation).** Take t > 0, k ≥ 0 and n_0 = N+1. Put u = A B^{n_0} n_0^k t^{n_0-k} / Γ(1+a n_0) and r = Bt (1+1/n_0)^k Γ(1+a n_0)/Γ(1+a n_0 + a). If r < 1, then

    |d^k/dt^k (φ - P_N)(t)| ≤ u/(1-r).

*Proof.* The k-th derivative of (it)^n has modulus at most n^k t^{n-k}, and c_n ≤ A B^n/Γ(1+an) by Lemma 1. The ratio of consecutive majorant terms is Bt (1+1/n)^k Γ(1+an)/Γ(1+an+a). This ratio decreases in n, because log Γ is convex, so Γ(x+a)/Γ(x) increases in x. The majorant is therefore bounded by a geometric series. ∎

**Lemma 3 (Taylor cells).** Let K be even, t_c > 0 and |δ| ≤ h. Then

    |φ(t_c+δ)| ≤ Σ_{k<K} |φ^{(k)}(t_c)| h^k/k! + E[L^K] h^K/K!.

Each φ^{(k)}(t_c) is enclosed as P_N^{(k)}(t_c) plus the bound of Lemma 2.

*Proof.* This is Taylor's theorem with |φ^{(K)}| ≤ E|L|^K, and E|L|^K = E L^K = K! m_K/Γ(1+aK) because K is even. ∎

The code uses K = 40. It covers [0, T3'] by cells [2jh, 2(j+1)h], with h dyadic. On each cell the bound is s_j = min(1, the bound above).

**Lemma 4 (bootstrap tail bound).** Let T2 > 0 and T3 = 2^a T2. Let s be a step function with |φ| ≤ s on [0, T3]. Let β > 3 with aβ > 1, and let C satisfy s(t) ≤ C t^-β on [T2, T3]. Define

    R = T2^{-1/a} Σ_{cells ⊂ [0,T2]} s_j (1 - (r_j/T2)^{1/a}/2)^{-aβ} (r_j^{1/a} - l_j^{1/a})
        + 2^{aβ} C T2^-β / (aβ - 1).

If R < 1, then |φ(t)| ≤ C t^-β for all t ≥ T3.

*Proof.* Let b = s on [0, T3) and b = C t^-β on [T3, ∞). Then b ≤ C t^-β on [T2, ∞).

*Step 1: J(t) ≤ R b(t) for t ≥ T3.* Put J(t) = ∫_0^1 b(tv^a) b(t(1-v)^a) dv = 2∫_0^{1/2} (same). For v ≤ 1/2 the larger argument satisfies t(1-v)^a ≥ 2^{-a}t ≥ T2. So b(t(1-v)^a) ≤ C t^-β (1-v)^{-aβ}, and J(t)/b(t) ≤ 2∫_0^{1/2} b(tv^a)(1-v)^{-aβ} dv. Split this at v_0 = (T2/t)^{1/a} ≤ 1/2.

- On v < v_0, substitute u = tv^a. The piece becomes

      (2/a) t^{-1/a} ∫_0^{T2} s(u) (1-(u/t)^{1/a})^{-aβ} u^{1/a-1} du.

  The integrand is pointwise decreasing in t. At t = T3, where t^{-1/a} = T2^{-1/a}/2, it is at most the first term of R: on each cell, take the weight at the right end r_j, and use ∫_l^r u^{1/a-1} du = a(r^{1/a} - l^{1/a}).
- On v ≥ v_0, bound b(tv^a) ≤ C t^-β v^{-aβ} and (1-v)^{-aβ} ≤ 2^{aβ}. The piece is at most

      2^{1+aβ} C t^-β v_0^{1-aβ}/(aβ-1) = 2^{1+aβ} C T2^-β (T2/t)^{1/a}/(aβ-1).

  This decreases in t and equals the second term of R at t = T3.

So J(t) ≤ R b(t) < b(t) for every t ≥ T3.

*Step 2: continuity argument.* Let σ = sup{τ ≥ T3 : |φ| ≤ b on [0, τ]}, and suppose σ < ∞. By continuity, |φ| ≤ b on [0, σ]. By (2.1), whose arguments lie in [0, σ],

    |φ(σ)| ≤ J(σ) < b(σ).

Both |φ| and b are continuous on [T3, ∞), so |φ| < b on a neighbourhood of σ. This contradicts the choice of σ. ∎

This is an explicit, self-improving version of GLR Step 4 (proof of Thm 2.5). The constants are computed rather than existential.

**Lemma 5 (formula for f''(0)).** Lemma 4 makes t^2 φ integrable. Then f ∈ C^2 and

    f''(0) = -(1/π) ∫_0^∞ t^2 Re φ(t) dt = -(1/π) [I(T3) + E],

with

    I(T3) = Σ_{n even ≤ N} (-1)^{n/2} c_n T3^{n+3}/(n+3) ± (T3^3/3) · (Lemma 2 bound at T3, k = 0),
    |E| ≤ C T3^{3-β}/(β-3).

*Proof.* Use Fourier inversion with differentiation under the integral, which is justified by dominated convergence, and φ(-t) = conj φ(t). The integral of P_N is exact term by term. The truncation bound of Lemma 2 increases in t, so its value at T3 bounds it on [0, T3]. ∎

**Corollary (modality).** g_a''(0) = f_a''(0). Assume the companion theorem: g_a is symmetric and has at most two modes. If f_a''(0) < 0, then 0 is a strict local maximum of g_a, a third maximum is excluded, and g_a is unimodal. If f_a''(0) > 0, then 0 is a strict local minimum, and g_a is bimodal.

## 4. What is certified (commands, ranges, precision)

All commands run from `scripts/`. The driver uses β = 4 and K = 40. It climbs a ladder T2 ∈ {1/2, 1, 2, 3, 4, 6, 8, 10, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384}. For each T2 it sets:

- h = 1/32, doubled while 2h ≤ T2/160;
- N = the least value (step 100, starting at 400) with N log(B T3) + 40 log N - lgamma(1+aN) < -350;
- precision = 1.45 (B T3)^{1/a} + 600 bits.

It reports a sign only when R < 1, aβ > 1, and the whole enclosure lies on one side of 0. N and the precision are chosen from float estimates, but this choice affects only whether a run succeeds, never correctness. The printed lines give N, precision, T2, T3, h, R, C, E and B.

1. `py -I certify_fpp.py scan` writes `data/scan_output.txt`. It runs in 215 s and exits 0. It certifies 40 values of a, at grid steps of 0.01 or 0.02 with extra points near the threshold:
   - sign -1 at a = 0.501, 0.505, 0.51, 0.52, 0.53, ..., 0.66, 0.665, 0.668;
   - sign +1 at a = 0.669, 0.67, 0.675, 0.68, 0.69, 0.70, 0.72, ..., 0.96, 0.97.

   Examples:
   - f''(0) at 0.501 is -3.5619679e-5 (radius < 1e-12);
   - at 0.668 it lies in [-5.5605e-4, -5.5537e-4];
   - at 0.669 it lies in [1.2873e-4, 1.2958e-4];
   - at 0.95 it lies in [0.21798, 0.22139].
2. `py -I certify_fpp.py bisect 0.6688 0.6689 30` writes `data/bisect_output.txt`. It runs in 160 s and exits 0. All 32 evaluations are certified, and the final bracket (a_1, a_2) is as in Section 1. Near the threshold the runs use T2 = 10 to 12 (T3 ≈ 16 to 19), N = 1300 to 1500 and about 800 to 870 bits. The total error from tail and truncation there is below 2e-24.
3. `py -I certify_fpp.py point 0.98` writes `data/point_0.98_output.txt`. It is **not certified**: it exits 1, because the ladder stops at T2 = 384 and at T3 ≈ 757 the polynomial tail E is still about 2e2.
4. `py -I check_moments.py` writes `data/check_moments_output.txt`, and all checks pass.

## 5. Numerical evidence only

- **Location of a_c.** The bisection enclosures give a_c ≈ 0.6688128600146. The slope near the threshold is about 0.69, which gives f''(a_2) ≈ 4.2e-16.
- **Density check.** `check_density_float.py` writes `data/check_density_float_output.txt`. It compares the Fourier density f_{0.6688}(x) with (n^a/2) P(S_n = j) at n = 8000. They agree to within 4% at x ∈ {-1, 0, 0.5, 1, 2, 3}, consistent with the slow finite-n convergence. This checks that the series is the right object.
- **Decay of φ.** |φ_a(t)| decays like exp(-c t^{1/a}) at a = 0.6688 (for example 3.7e-18 at t = 10). The decay is slow near a = 1 (1.8e-5 at t = 100 for a = 0.95), which is why the cost there rises.
- **Near a = 1/2.** At a = 0.501 the certified f''(0) = -3.562e-5. The Gaussian value with the exact mean and variance, -(2π)^{-1/2} σ^{-3} (1 - μ^2/σ^2) e^{-μ^2/2σ^2}, is -3.576e-5. This suggests f''(0) σ^3 → -(2π)^{-1/2} as a ↓ 1/2.
- **Near a = 1.** The certified f''(0) at a = 0.95 to 0.97 is positive and decreasing (about 0.22, 0.19, 0.15), consistent with f''(0) → 0+ as a → 1.

## 6. What remains (first missing step first)

1. **Interval covering in a. This is the first missing step.** Each certificate holds only at its exact rational a. To prove a sign on [0.501, a_1] and [a_2, 0.97], one needs a rigorous modulus of continuity for a ↦ f_a''(0) between grid points. The same estimate, as continuity alone, is also what turns "the sign differs at a_1 and a_2" into "a zero lies in (a_1, a_2)".
   - **Why direct balls fail.** Evaluating the series with a as a ball does not work. The moment series cancels terms of size e^{(BT3)^{1/a}}, about 1e60 near the threshold, so the a-boxes would need width around 1e-65.
   - **Route 1.** Bound ∂_a φ_a(t) uniformly on an a-box. Small t would use the series in a cancellation-free form, for example the Hankel-contour representation Ψ(it) = (2πi)^{-1} ∫ e^u u^{-1} M(it u^{-a}) du with GLRS's closed form for M. Large t would use a version of Lemma 4 that is uniform in a. This is the next thing to build.
   - **Route 2.** Prove the monotonicity of a ↦ f_a''(0). That looks harder.
2. **The end a ↓ 1/2.** The certified range starts at 0.501. One route is a local CLT in C^2 with explicit rate: σ_a L_a → N(0,1) with σ_a^2 = Var L_a ~ 1/(2a-1), together with tail bounds on φ that are uniform in a. Because Bt stays bounded on the relevant scale t ~ 1/σ, Lemmas 1 to 4 look uniformizable. This is not done.
3. **The end a ↑ 1.** The certified range stops at 0.97. Pushing the grid further costs T3 ~ 1/(1-a). An analytic argument is needed that f_a is convex at 0 when L_a concentrates near 1. Concentration alone does not give convexity at a point in the left tail. Possible tools are the tail asymptotics of GLRS Thm 1.3 made uniform in a, or the integral equation of GLR Remark 2.7. Not attempted.
4. **The companion theorem.** It is used only through the Corollary of Section 3. Nothing here proves it.
