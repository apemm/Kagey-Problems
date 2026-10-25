# Paper D threshold certificate, part 3: audit

Date: 2026-10-25. Scope: `01_report.md`, `02_report.md`, `scripts/`, `data/`, checked against Paper D, Section 4 (Theorems 4.2 and 4.3 in `sec_bulk_applications.tex`) and the GLR text in `sources/`. Only the mathematics and the code were judged. No file in this folder was changed except this one. Every rerun used `py -I -B`, so no `__pycache__` was written into `scripts/`.

## Claim audited

1. Case (a) of Theorem 4.2 holds for a in (1/2, z_-], via f''(0) < 0.
2. Case (b) holds for a in [z_+, 0.6712], via f''(0) > 0.
3. Case (b) holds for a in [0.6705, 1), via the Hankel test.

Here z_- = 1838418790980431/2748779069440000 and z_+ = 45960469774511/68719476736000.

## Verdict

**Proved as written.** The proof assumes Theorem 4.2 and four inputs from GLR: the fixed point (Thm 1.1), the moment recursion (Thm 1.4), the continuous density (Thm 1.3) and a finite MGF (Cor 2.11). I found no missing implication. Two remarks on the code and one on provenance are listed at the end. None of them affects the result.

## 1. Uniform tail bound (Lemma 4, and Lemma 8 with T3 >= 2^a T2)

I re-derived this from scratch. Take a in I and T3 >= 2^a T2. Put b = s on [0, T3) and b = C t^-β on [T3, ∞).

- **b is below the power law on [T2, ∞).** C is the maximum of s_j r_j^β over the cells that meet [T2, T3], and t <= r_j on each cell. So s <= C t^-β on [T2, T3]. The cell that contains T3 gives |φ(T3)| <= C T3^-β, so |φ| <= b on [0, T3] to start with.
- **The larger argument is past T2.** For v <= 1/2 and t >= T3, t(1-v)^a >= 2^-a T3 >= T2. So b(t(1-v)^a)/b(t) <= (1-v)^-aβ. Also v_0 = (T2/t)^{1/a} <= (T2/T3)^{1/a} <= 1/2.
- **The piece v < v_0.** Substitute u = t v^a, which gives dv = (1/a) t^{-1/a} u^{1/a-1} du. For t >= T3,
  - t^{-1/a} <= T3^{-1/a} <= T2^{-1/a}/2;
  - 1 - (u/t)^{1/a} >= 1 - (u/T2)^{1/a}/2;
  - the weight increases in u, so its value at the right end of each cell bounds it on the cell.

  The piece is therefore at most T2^{-1/a} Σ s_j w(r_j)(r_j^{1/a} - l_j^{1/a}), which is the first term of R.
- **The piece v >= v_0.** The bound is 2·2^{aβ} C t^-β v_0^{1-aβ}/(aβ-1) = 2^{1+aβ} C T2^-β (T2/t)^{1/a}/(aβ-1). This is at most 2^{aβ} C T2^-β/(aβ-1), which is the second term of R.
- **The continuity step.** It is sound. Every argument used in (2.1) lies in [0, σ], b is continuous on [T3, ∞), and |φ| is continuous. Inequality (2.1) needs only independence and |φ(-s)| = |φ(s)|, both of which GLR (1.5) and (2.10) give.

The code (`erw_tm.certify`) matches this:

- T3 = upper(2^{a_hi} T2);
- the cells [0, T2] are cells[:n2], with T2 = 2h n2 checked exactly;
- the cells reach past T3;
- R is evaluated with a as a ball over I. Dependency only widens the ball. C and the cell values s_j are suprema over I.

The cell bound is Lemma 3 with Kt = 12, which is even, and the remainder is sup_S |c_12| h^12 >= E L^12 h^12/12!.

## 2. Scaled variable near a = 1/2 (Lemma 9)

- **The exponents.** ⌊n/2⌋ - ⌊j/2⌋ - ⌊(n-j)/2⌋ is 1 when n is even and j is odd, and 0 otherwise. With μ_2 = a, the recursion code matches term by term:
  - for odd n, the pairs carry (1+a) and the denominator is (n-1)z;
  - for even n, odd j carries a·y and the denominator is nz - 1.
- **Analyticity.** The denominators vanish only at a = 0 and a = 1/n <= 1/4, so μ_n is analytic for Re a > 1/4. The code asserts α > 0.3.
- **The factor sqrt(yΓ(2a)).**
  - m_n σ^{-n} = μ_n Γ(2a)^{⌊n/2⌋} for even n, and μ_n Γ(2a)^{⌊n/2⌋} sqrt(yΓ(2a)) for odd n.
  - For real a, the even part E is real and the odd part O is purely imaginary. So |φ_X| <= sqrt(E² + f²|O|²), with f = sup over real I of sqrt(yΓ(2a)).
  - The code bounds this by Σ_i w^i sqrt(E_i² + f² O_i²) plus max(1,f)·(Cauchy and truncation bounds). That is the triangle inequality for the vectors (E_i, f O_i).
  - The factor never has to be evaluated at complex a, because E and O each get their own Cauchy bound, and those bounds are dominated by Σ_n sup_S |c_n| ....
- **The complex form of Lemma 1.**
  - The constant κ = max(1,|z|)·max(1,|y|) bounds |c_j y^{e_j}|.
  - |nz - c_n| >= nα - 1, using α <= 1 for odd n.
  - |Γ(2z)|^{⌊n/2⌋} <= Gm^{n/2} with Gm >= 1.
- **The fixed-point equation.** It is linear, so X = L/σ satisfies it.
- **The limit.** At a = 1/2, G → -(2π)^{-1/2}.
- **The sign.** The sign of G is the sign of f''(0), since σ³ > 0.

## 3. Taylor models in a (Lemmas 6 and 7)

- **The Gamma bound.** |Γ(x)/Γ(x+iy)|² = Π(1 + y²/(x+k)²) <= exp(y²(1/x² + 1/x)). With x >= 1+nα and |y| <= nρ this gives Ã and B̃ as stated. Γ is increasing past 1.4616.
- **The Cauchy step.** Only finite sums have to be analytic on the disc: F^N(z) and ∂_t^k P_N(z, t_c). Their sup is bounded by Σ_n sup_S |c_n| (...), which is a sum of acb enclosures with no cancellation. No complex-a tail and no complex-a fixed point is needed. The truncation tail and the bootstrap are used only for real a ∈ I ⊂ S. So the obstruction noted in 02, §5 (no fixed point for complex a) does not arise.
- **The Taylor coefficients.** They are computed at the exact centre by arb_series, and the remainder is M q^{K+1}/(1-q). The square contains the disc. In the non-scaled case the code asserts |z| <= 1 on the square, which is the hypothesis |c_j| <= 1.

## 4. Hankel test (Lemma 10)

- **Case (a) gives a moment sequence.** In case (a), g_a is even and nonincreasing on [0, ∞), so the law of L° is unimodal about 0. A flat top is allowed. Khinchine then gives L° = U Z.
  - E L°^{2j} = E L^{2j}, because L° = ±L with a fair sign.
  - So s_j = (2j+1) E L^{2j} = E (Z²)^j, and every moment is finite.
  - Then x^T H0 x = E(Σ x_i W^i)² >= 0 and x^T H1 x = E W(Σ x_i W^i)² >= 0, with W = Z² >= 0.
- **Which matrix the test uses.** Both conditions are necessary, so one negative form suffices. Every recorded box uses H0.
- **From not-(a) to (b).** Theorem 4.2 says "exactly one of (a), (b)", so ruling out (a) gives (b).
- **The code.** The Taylor model in `check_box_tm` is as in §3. Denominators stay away from 0 because a0 - ρ >= 1/2 + (a0 - 1/2)/10. 1/Γ is entire, so a disc that crosses a = 1 is harmless.

## 5. Moment recursion

- **Against GLR.** `sources/glr_fixed_point.txt`, Thm 1.4: m_k = (ka - c_k)^{-1} Σ c_j m_j m_{k-j}, with E L^k = (k-1)! m_k/(aΓ(ka)) = k! m_k/Γ(1+ka), and MGF Σ m_k t^k/Γ(1+ka). This is the formula the code uses.
- **Independent check.** I ran the exact ERW moment dynamics (S_1 = +1, E[X_{n+1} | F_n] = a S_n/n) up to n = 6.4·10^5 at a = 9/10, with Richardson extrapolation in n^{1-2a}. E L^k for k = 1, ..., 6 converges to the GLR values: to 3·10^-8 for k = 1 and to about 1·10^-5 relative for k = 6.

## 6. From f''(0) to the cases

- **Smoothness.** Lemma 4 gives |φ| <= C t^-4, so f ∈ C² and g''(0) = f''(0).
- **f''(0) < 0.** Then g' < 0 on (0, δ). That contradicts (b), where g is nondecreasing on [0, c].
- **f''(0) > 0.** Then g' > 0 on (0, δ). That contradicts (a).

Plateaus elsewhere do not matter. The inference is correct as stated.

## 7. Coverage

I read every data file.

- **The scaled runs** cover 1/2 to 167/250 (0.668) in 40 intervals. They join end to end, and each run prints "contiguous cover: True" and exit 0.
- **The zero run** covers 167/250 to 839/1250 (0.6712).
  - Its undecided piece is exactly [z_-, z_+].
  - The sign is - on pieces that end at z_- and + on pieces that start at z_+. The pieces are closed balls, so f''(z_-) < 0 and f''(z_+) > 0.
- **The Hankel run** `hankel_output_06705.txt` covers 1341/2000 (0.6705) to 1 in 115 boxes, with exit 0. The boxes come from recursive bisection of exact rational edges, so they leave no gaps.
- **The ends.** The cover reaches a = 1/2 exactly through the scaled variable, and a = 1 is a box endpoint, so (1/2, z_-], [z_+, 0.6712] and [0.6705, 1) are covered.
- **The tightest margin** is on [0.6700, 0.6704]: η = 7.4e-4 against G ≈ 8.3e-4 to 1.1e-3. The sign is still decided.

## 8. Reruns and independent reimplementation

- **The repo scripts, read only.**
  - `certify_interval.py scaled 0.5 0.50375` reproduces η = 0.0768 and G0 = -0.398726 exactly, in 103 s.
  - `certify_interval.py cover 0.6704 0.6708 1 1/100` reproduces the stored line exactly (η = 7.76e-4, G0 = 1.25212e-3).
- **Own pointwise f''(0) code.** It implements Lemmas 1 to 5 with different parameters: h = 1/128, Taylor order 24 in t, β = 4.
  - At a = 3/5: f''(0) = -0.019760816 ± 4e-10 with R = 0.027. This matches the scaled G at 0.6 divided by σ³, which is about -0.2511/12.71.
  - At a = 0.6702: f''(0) = 9.68e-4 ± 7.5e-7. This matches G0 = 9.68239e-4 at the centre of [0.6700, 0.6704].
- **Own Hankel code.**
  - Pure interval arithmetic in a certifies Q < 0 on [0.72, 0.7205] (k = 4, H0) and on [0.95, 1] (k = 1).
  - At k = 40 near 0.6712, pure interval arithmetic fails: the enclosure is ±1e23. This confirms that Taylor models are needed there.
  - My own Taylor model, with K = 82 and remainder 5.5e-41, certifies Q < 0 on the first stored box [839/1250, 322193/480000] at k = 40. The upper bound on Q is -9.9e-10, and Q(centre) = -2.7131e-9, the stored value.

## Remarks (none affects the result)

1. **Provenance.** `interval_scaled_0.50_0.53.txt` records N = 1200 and prec = 900. The current `certify_interval.py` cannot produce prec < 1100. My rerun of the first interval with the current code used N = 1400 and prec = 1335, and gave the same η and G0. The stored file therefore comes from an earlier parameter choice. Regenerate it before archiving.
2. **A missing guard in `hankel_certify.check_box_tm`.** It sets ρ = min(w/q, 0.9(a0 - 1/2)) without checking qq = w/ρ < 1. If qq >= 1, the remainder M qq^{K+1}/(1-qq) would be negative and the check unsound. On the recorded boxes qq <= 0.27, so the defect is not triggered. Add `assert qq < 1`.
3. **Superseded wording in `01_report.md`.** Its Corollary ("a third maximum is excluded") is informal and is replaced by 02, §0. The case inference in 02, §0 is the correct one.
