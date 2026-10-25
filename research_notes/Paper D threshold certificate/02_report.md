# Paper D threshold certificate, part 2: intervals of a, both ends

Date: 2026-10-25. This continues `01_report.md`, which is kept as it was. The lemma numbers continue from there: Lemmas 1 to 5 are in 01, and Lemmas 6 to 10 are below.

New files:

- `scripts/erw_tm.py`: Taylor models in a with Cauchy remainders, in the original variable and in the scaled variable (Lemmas 6 to 9).
- `scripts/certify_interval.py`: the driver for whole intervals of a. It has modes `cover`, `zero` and `scaled`.
- `scripts/hankel_certify.py`: the moment certificate that the law is not unimodal (Lemma 10).
- `data/interval_*.txt` and `data/hankel_output.txt`: the stored outputs (Section 5).

Software is as in 01. Every run uses `py -I`.

## 0. How the result fits Paper D's Theorems 4.2 and 4.3

Theorem 4.2 (`thm:two-modes`, sec_bulk_applications.tex) says that exactly one of two cases holds for every a in (1/2, 1):

- **(a)** g_a is nondecreasing on (-∞, 0] and nonincreasing on [0, ∞);
- **(b)** there is c > 0 such that g_a is nondecreasing on [0, c] and nonincreasing on [c, ∞), and g_a(0) < g_a(c).

All the statements below are statements about which case holds.

- **f''(0) < 0 gives (a).** Then 0 is a strict local maximum of g_a. Case (b) is impossible, because there g_a is nondecreasing on [0, c].
- **f''(0) > 0 gives (b).** Then 0 is a strict local minimum. Case (a) is impossible, because there g_a is nonincreasing on [0, ∞).
- **A failed Hankel test gives (b).** If case (a) holds, g_a is unimodal about 0. Lemma 10 shows that a failed Hankel test rules that out, so (b) holds.

Theorem 4.3 (`thm:two-modes-near-one`) gives (b) for a ≥ 39/40. Its proof uses concavity of P(|L| ≤ t), Cantelli and Chebyshev. Lemma 10 is a sharper form of the same idea: Khinchine's representation plus a quadratic form in the even moments. It replaces the threshold 39/40 by the value of a_H in Section 4, so [0.97, 39/40] is covered. Theorem 4.3 is not redone here.

## 1. Results

[filled in Section 5 after the runs]

## 2. Uniform enclosures on intervals of a (gap 1)

**Why a point method is needed.** In ball arithmetic with a as an interval, the moment series loses all accuracy, because it cancels terms of size e^{(BT)^{1/a}}, about 1e60 near a_c. The method below never puts an interval of a inside a sum that cancels. Fix a0 and w, and set I = [a0 - w, a0 + w], q ∈ (0, 1), ρ = w/q, and S = the closed square a0 + [-ρ, ρ] + i[-ρ, ρ] ⊃ the disc |z - a0| ≤ ρ.

**Lemma 6 (moments on a complex square).** Suppose Re z ≥ α > 1/2 and |z| ≤ 1 on S. Then m_n(z), defined by the recursion, is analytic on a neighbourhood of S. Suppose also that |m_j| ≤ A B^j on S for 1 ≤ j ≤ N, with A = ((N+1)α - 1)/N. Then for all n and all z ∈ S:

- |m_n(z)| ≤ A B^n;
- |c_n(z)| = |m_n(z)/Γ(1+nz)| ≤ Ã B̃^n / Γ(1+nα), with Ã = A e^{ρ²/(2α²)} and B̃ = B e^{ρ²/(2α)}.

*Proof.*

- *Analyticity and the bound on m_n.* The denominators satisfy Re(nz - c_n) ≥ nα - 1 > 0, so m_n is analytic. The bound on m_n is the induction of Lemma 1, using |c_j| ≤ max(1, |z|) = 1 and |nz - c_n| ≥ nα - 1.
- *The Gamma factor.* For x > 0, |Γ(x)/Γ(x+iy)|² = Π_{k≥0} (1 + y²/(x+k)²) ≤ exp(y²(1/x² + 1/x)). Take x = 1 + n Re z ≥ 1 + nα and |y| = n|Im z| ≤ nρ. Then n²/x ≤ n/α and n²/x² ≤ 1/α². Finally Γ(1 + n Re z) ≥ Γ(1 + nα), because Γ increases on [1.47, ∞). ∎

The code encloses m_n(S) and c_n(S) in acb ball arithmetic for n ≤ N, one coefficient at a time. Nothing cancels in these sums, since every term is a product of enclosures. It then checks the hypothesis of Lemma 6 in balls. The truncation bound of Lemma 2 carries over with (A, B, a) replaced by (Ã, B̃, α), uniformly on S, and the ratio is still monotone by log-convexity of Γ.

**Lemma 7 (Taylor model with Cauchy remainder).** Let h be analytic on a neighbourhood of the disc |z - a0| ≤ ρ, with |h| ≤ M there, and let h_i be its Taylor coefficients at a0. Then for real a ∈ I,

    |h(a) - Σ_{i≤K} h_i (a-a0)^i| ≤ M q^{K+1}/(1-q).

*Proof.* Cauchy's estimate gives |h_i| ≤ M ρ^{-i}. Sum the geometric tail with |a - a0| ≤ w = qρ. ∎

The method applies this to the following functions.

- **The integral.** F^N(z) = Σ_{n even ≤ N} (-1)^{n/2} c_n(z) T3^{n+3}/(n+3), the exact integral of t² Re P_N over [0, T3]. Here M = Σ |c_n|_S T3^{n+3}/(n+3).
- **The cell values.** For each cell centre t_c and k < 12, the derivatives ∂_t^k P_N(z, t_c). Here M = Σ |c_n|_S n^{(k)} t_c^{n-k}, where n^{(k)} is the falling factorial.

The coefficients h_i are computed at the point a0 by arb_series arithmetic on the recursion, with ε = a - a0 as the series variable. The cancellation then happens in each coefficient, at the exact point a0, and precision handles it as in 01. K is chosen so that M q^{K+1} ≤ e^{-60}.

**Lemma 8 (uniform tail on I).** For each cell [t_c - h, t_c + h] ⊂ [0, T3], the following bound holds for every a ∈ I:

    sup_{a∈I} |φ_a(t)| ≤ s := Σ_{k<12} [ Σ_{i≤K} w^i |∂_t^k P_{N,i}(t_c)| + M_k q^{K+1}/(1-q) + τ_k(t_c) ] h^k/k!
                           + sup_S |c_12| · h^12.

Here P_{N,i} is the i-th Taylor coefficient in ε, M_k is the Cauchy bound for the k-th t-derivative, τ_k is the uniform truncation bound, and sup_{a∈I} E L_a^{12}/12! ≤ sup_S |c_12|. Next take T3 ≥ 2^a T2 for all a ∈ I, that is T3 = 2^{a0+w} T2, and evaluate R of Lemma 4 with a as a ball over I. If R < 1, then |φ_a(t)| ≤ C t^-β for all t ≥ T3 and all a ∈ I.

*Proof.* The cell bound is Lemma 3 with each derivative bounded uniformly in a by Lemma 7. For Lemma 4 with T3 ≥ 2^a T2:

- the larger argument satisfies t(1-v)^a ≥ 2^{-a}T3 ≥ T2;
- at t = T3, v_0 = (T2/T3)^{1/a} ≤ 1/2, and 1 - (u/t)^{1/a} ≥ 1 - (u/T2)^{1/a}/2;
- T3^{-1/a} ≤ T2^{-1/a}/2.

So both terms of R bound the true ratio for every t ≥ T3. R depends on a only through the exponents 1/a and aβ, where a ball over I gives no cancellation. ∎

**Theorem A (interval enclosure).** For every real a ∈ I,

    f_a''(0) ∈ G(a - a0) ± η,   with G_i = -(1/π) F^N_i,
    η = (1/π) [ M_F q^{K+1}/(1-q) + (T3³/3) τ_0(T3) + C T3^{3-β}/(β-3) ].

Moreover a ↦ f_a''(0) is continuous on I.

*Proof.* The enclosure is Lemma 5 combined with Lemmas 7 and 8. For continuity: φ_a(t) is continuous in a for each t, since the series converges locally uniformly in a. By Lemma 8, t² |φ_a(t)| is dominated uniformly for a ∈ I by an integrable function. Dominated convergence then makes the Fourier integral continuous in a. ∎

The sign is decided by evaluating the polynomial G on sub-balls of I and bisecting while undecided. Each piece then has a certified sign, or, in `zero` mode, one single undecided piece remains.

## 3. The end near 1/2: the scaled variable (gap 3)

**Lemma 9 (scaled moments are analytic at a = 1/2).** Put y = 2a - 1 and μ_n = m_n y^{⌊n/2⌋}. Then:

- μ_0 = μ_1 = 1 and μ_2 = a;
- for n ≥ 3,

      μ_n (na - c_n) = Σ_{j=1}^{n-1} c_j μ_j μ_{n-j} y^{e_j},   with e_j = 1 if n is even and j is odd, and e_j = 0 otherwise.

The denominators are (n-1)a for odd n and na - 1 for even n ≥ 4. So every μ_n is a polynomial in a divided by a product of such factors, and it is analytic for Re a > 1/4.

Now let X = L/σ with σ² = E L² = 1/(y Γ(2a)), and put c_n = μ_n Γ(2a)^{⌊n/2⌋}/Γ(1+an). Then

    φ_X(u) = Σ_{n even} c_n (iu)^n + (y Γ(2a))^{1/2} Σ_{n odd} c_n (iu)^n,
    f_a''(0) = -(1/(π σ³)) ∫_0^∞ u² Re φ_X(u) du.

*Proof.*

- *The recursion.* Multiply the recursion for m_n by y^{⌊n/2⌋}. Then ⌊n/2⌋ - ⌊j/2⌋ - ⌊(n-j)/2⌋ equals 1 exactly when n is even and j is odd, and 0 otherwise. The case n = 2 is m_2 = a/y.
- *The series for φ_X.* The coefficients are m_n σ^{-n} = m_n (yΓ(2a))^{n/2} = μ_n Γ(2a)^{⌊n/2⌋} (yΓ(2a))^{(n mod 2)/2}.
- *The formula for f''(0).* Substitute t = u/σ. ∎

The fixed-point equation is linear and homogeneous, so X satisfies it as well, and (2.1) and Lemmas 1 to 8 apply to X. The adjustments in the scaled case are:

- Lemma 1 and Lemma 6 change only in the constant A = ((N+1)α - 1)/(Nκ), with κ = max(1, |z|) max(1, |y|) on S;
- the factor |Γ(2z)|^{1/2} enters B̃;
- the odd part is weighted by sqrt(y Γ(2a)), which is at most f = sup_I (y Γ(2a))^{1/2} for real a ∈ I, and in the Cauchy remainders at most max(1, f).

Because Lemma 9 needs only Re z > 1/4, the disc may cross a = 1/2. The real interval may then start exactly at a = 1/2, where X is N(0,1) and ∫ u² e^{-u²/2} du = (π/2)^{1/2}, so G(0) ≈ -(2π)^{-1/2}/... ≈ -0.3989 in the units of the code. The sign of G is the sign of f''(0), since σ³ > 0.

## 4. The end near 1: moments rule out case (a) (gap 2)

**Lemma 10 (Hankel test).** Fix a, k ≥ 1 and x ∈ R^{k+1}, and put s_j = (2j+1) E L^{2j} = (2j+1)(2j)! m_{2j}/Γ(1+2ja). Suppose that

    Σ_{i,j} x_i x_j s_{i+j} < 0   or   Σ_{i,j} x_i x_j s_{i+j+1} < 0.

Then case (a) of Theorem 4.2 fails, so case (b) holds and g_a has exactly two modes.

*Proof.* In case (a), g_a is even and nonincreasing on [0, ∞), so L = ±L_a is unimodal about 0. By Khinchine's theorem, L = U Y in law, with U uniform on (0, 1) independent of Y. Hence E L^{2j} = E Y^{2j}/(2j+1), that is s_j = E[(Y²)^j]. The two sums are then

    E[(Σ x_i Y^{2i})²] ≥ 0   and   E[Y² (Σ x_i Y^{2i})²] ≥ 0,

which contradicts the hypothesis. ∎

How the certificate is checked:

- `hankel_certify.py` takes boxes of a, with exact rational ends.
- For each box it chooses k and x from a float eigenvector at the box centre. This choice is not part of the proof.
- It checks the quadratic form < 0 in arb ball arithmetic with a as a ball over the whole box. No cancellation problem arises here, because only moments up to order 4k+2 enter.
- It bisects a box when the check fails.

The order k must grow as a decreases, since no finite set of moments can prove case (a). The float thresholds below which the order-k test cannot succeed are:

| k   | 1      | 2      | 3      | 4      | 8      | 16     | 24     | 32     |
| --- | ------ | ------ | ------ | ------ | ------ | ------ | ------ | ------ |
| a_k | 0.7748 | 0.7314 | 0.7126 | 0.7020 | 0.6849 | 0.6761 | 0.6733 | 0.6719 |

These thresholds decrease towards a_c ≈ 0.66881, roughly like k^-1.2.

## 5. Certified runs, numerical evidence, what remains

[filled in after the runs]
