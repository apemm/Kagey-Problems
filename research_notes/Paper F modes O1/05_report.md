# Paper F, (O1), fifth round: Lemma 12 in full, the bell-shape input checked, and (EQ)

Date: 2026-10-25. This round closes the two items flagged in `04_report.md` §8, which is left
unchanged. Section numbers, lemma numbers and notation refer to 04.

## 0. Summary

1. **Lemma 12 is now proved** (§1). The proof needs (RV), (SPAN), (LD) and (LD2). The last
   two enter only for indices m of order at most j, through a second-difference version (D1′)
   of Lemma 8, which is proved here (§1.3).
   - The statement in 04 is corrected in one place: the dominant-factor tail (T1) must be
     weighted by the other kernel, not bounded by a plain supremum. Theorem 14 uses only the
     weighted form, so its proof is unchanged.
   - The sum over q-kernel shifts v > j/2 needs a summation by parts. A naive bound fails for
     α ≤ √2.
2. **Kwaśnicki checked against the full text** (arXiv v3, 27 Nov 2018) (§2).
   - Definition 2.1 and Corollary 1.3 ("All stable distributions on ℝ have bell-shaped density
     functions") give exactly the input needed, for every index and every skewness.
   - The definition does not exclude zeros without a change of sign. Analyticity closes this:
     for an analytic bell-shaped function, f^{(n)} has exactly n zeros and all of them are
     simple (Lemma 16). So h' ≠ 0 off the mode and h'' < 0 at the mode.
   - Nothing is missing. One caveat: I read the arXiv version, not the journal version.
3. **(EQ)** (§3).
   - "T_+/T_− converges to a positive constant" is a special case of (EQ), so it is stronger,
     not weaker.
   - (EQ) is equivalent to inf_N min_σ θ_{σ,N} > 0, and it is used only at the scale N.
   - So Theorem 1 holds along every sequence of N with min_σ θ_{σ,N} ≥ θ_0 > 0, with no global
     comparison of the tails. This includes equal indices with T_+/T_− oscillating unboundedly,
     restricted to the N where the two scales are comparable.
4. **Status.** Theorem 1 of 04 (the exact eventual count M_+ + M_− + 1 under (SPAN), (LR), (LD2)
   and (EQ)) is now proved in full, modulo audit.

## 1. Lemma 12, complete

**Notation.** Fix a sign and drop it: f, T, μ, a, u_m = f^{∗m}, S_n. Δ is the forward difference
in the level, and r ∈ {1, 2}. C and c depend only on the law. For x an integer and m ≥ 1, put
z = x − mμ. We write I_j(K) = {m : |j − mμ| ≤ K a(j/μ)} and A = a(j/μ).

### 1.1 Tools

- **(F1) Uniform bounds.** a(m)^{1+r}|Δ^r u_m(x)| ≤ C, and a(m)u_m(x) ≤ C (Lemma 11 and
  `lem:stable`(ii)).
- **(F2) Right tails.** P(S_n − nμ ≥ y) ≤ CnT(y) for all n ≥ 1 and y > 0.
  - *Proof.* If nT(y/8) ≥ 1, the bound holds with C = C_{1/8}, by Potter's bounds
    (`lem:rv`(ii)).
  - Otherwise P ≤ nT(y/8) + P(max X_i < y/8, S_n − nμ ≥ y)
    ≤ CnT(y) + e^{C_K}(nT(y/8))⁴ ≤ C'nT(y), by `lem:truncated` with w = y/8. ∎
- **(F3) Left tails.** P(S_n − nμ ≤ −y) ≤ e^{C_−}e^{−y/a(n)} (`lem:stable`(iv)).
- **(F4) Local right deviations.** u_n(nμ + y) ≤ CnT(y)/a(n) for y ≥ 1 (`lem:stable`(iii)).
- **(F5) Local left deviations.** u_n(nμ − y) ≤ Ca(n)^{−1}e^{−y/(2a(n))} for y ≥ 0.
  - *Proof.* For n = 1 the left side vanishes unless y < μ, so the bound holds with a constant.
    For n ≥ 2 write u_n = u_{n_1} ∗ u_{n_2} with n_1 = ⌊n/2⌋.
  - If S_{n_1} + S_{n_2} = nμ − y, then one block lies at least y/2 below its mean. Restricting
    the convolution to the two corresponding sets of x_1 gives
    u_n(nμ − y) ≤ sup u_{n_2}·P(S_{n_1} ≤ n_1μ − y/2) + sup u_{n_1}·P(S_{n_2} ≤ n_2μ − y/2).
  - Then apply (F1), (F3) and a(n_i) ≍ a(n). ∎
- **(F6) Mean absolute deviation.** E|S_n − nμ| ≤ Ca(n).
  - *Proof.* E(S_n − nμ)_+ ≤ a(n) + ∫_{a(n)}^∞ CnT(y)dy ≤ a(n) + Cna(n)T(a(n)) ≤ C'a(n), by (F2)
    and Karamata.
  - The negative part has the same mean. ∎

### 1.2 A pointwise bound and the total variation

**Lemma 12a.** Assume (RV) and (SPAN). For all m ≥ 1 and integers x:
- if z ≥ 0, then |Δ^r u_m(x)| ≤ Ca(m)^{−1−r} min{1, mT(z/4)};
- if z < 0, then |Δ^r u_m(x)| ≤ Ca(m)^{−1−r} e^{−|z|/(8a(m))}.

In addition, ‖Δu_m‖_1 ≤ C/a(m).

*Proof.* The bound with min{…} = 1 is (F1). For z ≥ 0 we may therefore assume
mT(z/4) ≤ 1 and z ≥ 24. For z < 0 we may assume |z| ≥ 24a(m).

**m ≤ 2.**
- For z < 0 we have x ≥ m, so |z| ≤ 2μ and there is nothing to prove.
- For z ≥ 0, |Δ^r u_1(x)| ≤ 4 max_{i≤2} f(x+i) ≤ 4T(x) ≤ CT(z/4).
- Also u_2(y) ≤ 2 sup_{y'≥y/2} f(y') ≤ 2T(y/2), which gives the same bound for m = 2.

**r = 1, m ≥ 2, z ≥ 24.** Write u_m = u_{(1)} ∗ u_{(2)}, with block sizes m_1 = ⌊m/2⌋ and
m_2 = m − m_1, means ν_i = m_iμ, and a(m_i) ≍ a(m). Put c = ⌈ν_1 + z/2⌉. Then
Δu_m(x) = Σ_{x_1} u_{(1)}(x_1)Δu_{(2)}(x − x_1).
- **Part x_1 ≥ c−1.** It is at most sup|Δu_{(2)}|·P(S_{m_1} ≥ c−1) ≤ Ca(m)^{−2}·CmT(z/3), by
  (F1) and (F2).
- **Part x_1 ≤ c−2.** Use the exact summation by parts
  Σ_{x_1≤c−2} u_{(1)}(x_1)[g(x+1−x_1) − g(x−x_1)]
  = Σ_{x_1≤c−3} Δu_{(1)}(x_1)g(x−x_1) − u_{(1)}(c−2)g(x−c+2),
  with g = u_{(2)}. Its first sum is at most sup|Δu_{(1)}|·P(S_{m_2} − ν_2 ≥ z/2 − 3). Its
  boundary term is at most u_{(1)}(ν_1 + z/2 + O(1))·sup u_{(2)} ≤ (CmT(z/3)/a(m))·(C/a(m)), by
  (F4).
- Since T(z/3) ≤ CT(z/4), the claim follows.

**r = 2, m ≥ 3, z ≥ 24.** Use three blocks with sizes ⌊m/3⌋ or ⌈m/3⌉, means ν_i, and cuts
c_i = ⌈ν_i + z/3⌉ for i = 1, 2. Split the sum over (x_1, x_2) into three regions, writing
u_{(23)} = u_{(2)} ∗ u_{(3)}.
- **(R1) x_1 ≥ c_1.** Write Δ²u_m(x) = Σ_{x_1} u_{(1)}(x_1)Δ²u_{(23)}(x−x_1). The part is at
  most P(S_{(1)} ≥ c_1)·sup|Δ²u_{m_2+m_3}| ≤ CmT(z/4)·Ca(m)^{−3}, by (F2) and (F1).
- **(R2) x_1 < c_1, x_2 ≥ c_2.** Write the part as
  Σ_{x_1<c_1}u_{(1)}(x_1)Σ_{x_2≥c_2}u_{(2)}(x_2)Δ²u_{(3)}(x−x_1−x_2). It is at most
  P(S_{(2)} ≥ c_2)·Ca(m)^{−3}.
- **(R3) x_1 < c_1, x_2 < c_2.** Then the third block lies above x − c_1 − c_2 ≥ ν_3 + z/3 − 2.
  Put H(y) = Σ_{x_2<c_2}u_{(2)}(x_2)u_{(3)}(y−x_2) and F(x) = Σ_{x_1<c_1}u_{(1)}(x_1)H(x−x_1).
  Summation by parts in x_1, as above, gives
  ΔF(x) = Σ_{x_1≤c_1−2}Δu_{(1)}(x_1)H(x−x_1) − u_{(1)}(c_1−1)H(x−c_1+1).
  Hence Δ²F(x) = Σ_{x_1≤c_1−2}Δu_{(1)}(x_1)ΔH(x−x_1) − u_{(1)}(c_1−1)ΔH(x−c_1+1). In the same
  way, ΔH(y) = Σ_{x_2≤c_2−2}Δu_{(2)}(x_2)u_{(3)}(y−x_2) − u_{(2)}(c_2−1)u_{(3)}(y−c_2+1).
  Expanding gives three kinds of terms:
  - (α) Σ_{x_1≤c_1−2, x_2≤c_2−2} Δu_{(1)}(x_1)Δu_{(2)}(x_2)u_{(3)}(x−x_1−x_2). This is at most
    ‖Δu_{(1)}‖_1·sup|Δu_{(2)}|·P(S_{(3)} − ν_3 ≥ z/3 − 4) ≤ (C/a)(C/a²)CmT(z/4).
  - (β) terms carrying the factor u_{(2)}(c_2−1). They are at most
    (‖Δu_{(1)}‖_1 + u_{(1)}(c_1−1))·u_{(2)}(c_2−1)·sup u_{(3)} ≤ (C/a)(CmT(z/4)/a)(C/a).
  - (γ) −u_{(1)}(c_1−1)Σ_{x_2}Δu_{(2)}(x_2)u_{(3)}(⋯). It is at most
    u_{(1)}(c_1−1)·‖Δu_{(2)}‖_1·sup u_{(3)} ≤ (CmT(z/4)/a)(C/a)(C/a).
  - Here u_{(i)}(c_i−1) is a local probability at deviation z/3 + O(1). Each term is at most
    Ca(m)^{−3}mT(z/4).

The total variation bound ‖Δu_{(i)}‖_1 ≤ C/a(m), used in (α)–(γ), is proved at the end of this
proof from the case r = 1.

**z < 0.** Mirror everything:
- the regions become x_1 ≤ c_1 = ⌊ν_1 + z/2⌋ (or ⌊ν_i + z/3⌋), and so on;
- the summation by parts runs over the upper-restricted sums;
- (F3) and (F5) replace (F2) and (F4).

The deviations are now at least |z|/3 − O(1) ≥ |z|/4, and e^{−|z|/(4·2a)} gives the stated
exponent.

**Total variation.** Use the r = 1 bound in its two-block form,
|Δu_m(x)| ≤ Ca^{−2}Σ_{i=1,2}P(|S_{m_i} − ν_i| ≥ |z|/2 − 3) + max u_{(1)}(·)·max u_{(2)}(·),
where the last two factors are local probabilities at ν_1 + z/2 + O(1) and ν_2 + z/2 + O(1).
Sum over x.
- The probabilities add up to at most Σ_x P(|S_{m_i} − ν_i| ≥ |x − mμ|/2 − 3)
  ≤ 4E|S_{m_i} − ν_i| + C ≤ Ca(m), by (F6).
- In the boundary products, each value of u_{(2)} is hit by at most two x, so they add up to at
  most 2 sup u_{(1)} ≤ C/a(m).
- Together with the factor a^{−2}, this gives ‖Δu_m‖_1 ≤ C/a(m). This step uses only the r = 1
  bound, so there is no circularity. ∎

### 1.3 Second differences in the big-jump range

**Lemma 12c ((D1′)).** Assume (LR) and (LD2). There are K_1 and L_0 such that, for all m ≥ 1 and
all n with L = n − mμ ≥ max(K_1a(m), L_0),
|∇²u_m(n)| ≤ Cm f(L)/L² and |∇u_m(n)| ≤ Cm f(L)/L.

*Proof.* The first-difference bound is Lemma 8 (D1). For the second difference, follow the proof
of Lemma 8 with w = ⌈δL⌉ and δ smaller.

**No summand ≥ w.** Write f_w^{∗m} = f_w^{∗m_1} ∗ f_w^{∗m_2}. Then
∇²f_w^{∗m} = (∇f_w^{∗m_1}) ∗ (∇f_w^{∗m_2}), exactly. Split the convolution according to which
block lies above its mean by L/2 − O(1).
- On the part where block 1 deviates, the sum is at most
  sup|∇f_w^{∗m_2}|·Σ_{y dev}|∇f_w^{∗m_1}(y)|.
- Here Σ_{y dev}|∇g(y)| ≤ Σ_{y dev}(g(y) + g(y−1)) ≤ 2P(dev), since g ≥ 0.
- The other block is the same.
- With sup|∇f_w^{∗m'}| ≤ Ca(m)^{−2} (the Fourier bound of Lemma 8, step (1)) and `lem:truncated`,
  this part is at most Ca(m)^{−2}(mT(δL))^{1/(5δ)}.
- Relative to m f(L)/L² ≥ c(L/a)^{−α−ε}L^{−3}, the ratio is at most C(L/a)^{4+α+ε−(α−ε)/(5δ)},
  using a(m) ≤ L. This tends to 0 as K_1 → ∞, provided δ < (α−ε)/(5(4+α+ε)).

**A giant summand, first index I = i.** The second difference of
Σ_z h_i(z)f(n′−z)1{n′−z ≥ w} is Σ_{z≤n−2−w} h_i(z)∇²f(n−z) plus the two boundary terms of
Lemma 4(v):
- h_i(n−1−w)(f(w+1) − f(w));
- f(w)[h_i(n−w) − h_i(n−1−w)].

These are bounded as follows.
- In the main sum, n − z ≥ w = δL. So |∇²f(n−z)| ≤ C_δ f(L)/L², by (LD2) and Potter's bounds,
  and Σ_z h_i ≤ 1.
- **First boundary term.** h_i(n−1−w) ≤ u_{m−1}(n−1−w) ≤ CmT(L)/a(m), by (F4) at deviation at
  least L/2. Also |f(w+1) − f(w)| ≤ C_δ f(L)/L. Summed over i ≤ m, this is at most
  Cm²T(L)f(L)/(a(m)L). Relative to m f/L², it is CmT(L)L/a(m) ≤ C(L/a)^{1−α+ε} → 0.
- **Second boundary term.** h_i is the law of a sum of m−1 independent variables, i−1 of them
  truncated at w. The proof of (D1) applies to it at the level n − w, whose deviation is at
  least (1−2δ)L ≥ K_1a(m)/2: a truncated variable is never a giant at threshold w′ = δ(1−2δ)L
  < w. So |∇h_i(n−w)| ≤ Cm f(L)/L.
  The term is at most C_δ f(L)·Cm f(L)/L. Summed over i, relative to m f/L², this is
  Cm f(L)L ≤ CmT(L) → 0.
- **The sum over i.** Σ_i P(I = i) ≤ m, which gives Cm f(L)/L². ∎

### 1.4 The tail sums

**Lemma 12 (complete).** Assume (RV), (SPAN), (LD) and (LD2) for the sign, and let 𝗄 be one of
the kernels u_m, q_m, q_{m+1}.

- **(T2)** For K ≥ 2 and j → ∞,
  Σ_{m∉I_j(K)}|Δ^r𝗄_m(j)| ≤ C(K^{1−α+δ} + e^{−cK})A^{−r} + o(A^{−r}).
  For every i ≥ 1, Σ_m|Δ^r𝗄_m(i)| ≤ Ca(i)^{−r}.
- **(T1)** Fix ε > 0 and put m_ε = εN/(8μ_max). Uniformly in levels x ∈ [εN, N]:
  - |Δ^r𝗄_m(x)| ≤ Ca(N)^{−1−r} for m ≥ m_ε;
  - for m < m_ε,
    |Δ^r u_m(x)| ≤ Cm f(x)/x^r and |Δ^r q_m(x)|, |Δ^r q_{m+1}(x)| ≤ C f(x)x^{1−r}(1 + m/x).
- **(T1w)** Consequently, if 𝗄′ is a kernel of the other sign with 8m_εμ′ ≤ x′ ∈ [εN, N], then
  Σ_{m<m_ε}|Δ^r𝗄_m(x)|𝗄′_m(x′) = o(B_N^{−1−r}), and
  Σ_{m<m_ε}|Δ𝗄_m(x)||Δ𝗄′_m(x′)| = o(B_N^{−3}) whenever one of 𝗄, 𝗄′ is a u-kernel and the
  other a q-kernel. This is the case in every product of `eq:bulk-pairs`.

*Proof of (T2) for u.* Split m ∉ I_j(K) into three ranges.

- **(i) m ≤ j/(2μ).** Then L = j − mμ ≥ j/2 ≥ max(K_1a(m), L_0) for large j, since a(m) ≤ a(j)
  = o(j). By Lemma 12c (the case r = 1 is (D1)), |Δ^r u_m(j)| ≤ Cm f(j)/j^r, using
  f(L) ≤ Cf(j) for L ∈ [j/2, j] and shifts of r ≤ 2. Summing gives Cj²f(j)j^{−r} ≤ CT(j)j^{1−r}.
  - For r = 1: T(j)a(j) → 0, since α > 1/α.
  - For r = 2: T(j)a(j)²/j → 0, since α + 1 > 2/α.
  - So this range is o(A^{−r}). (Lemma 12a alone would require α > √2 here, through the
    smallest m. This is why (LD2) is needed.)
- **(ii) j/(2μ) < m < (j − KA)/μ.** Here m ≍ j and a(m) ≍ A. By Lemma 12a the terms are at most
  CA^{−1−r}mT(z/4), with z = j − mμ ≥ KA running over a progression of step μ. So
  Σ ≤ CA^{−1−r}·(j/μ)·[(1/μ)Σ_{z′≥KA−μ}T(z′/4) + T(KA/4)] ≤ CA^{−1−r}j·KA·T(KA), by Karamata
  `eq:karamata`. Since jT(A) → μ and T(KA) ≤ CK^{−α+δ}T(A), the range contributes at most
  CK^{1−α+δ}A^{−r}.
- **(iii) m > (j + KA)/μ.** The terms vanish unless m ≤ j + 2. For such m, a(m) ≍ A, and by
  Lemma 12a they are at most CA^{−1−r}e^{−(mμ−j)/(8CA)}. Summing the geometric-type series gives
  CA^{−r}e^{−cK}.

The total bound: the window contributes at most |I_j(2)|·CA^{−1−r} ≤ CA^{−r}, and ranges
(i)–(iii) with K = 2 contribute at most CA^{−r}. Small i are absorbed into the constant.

*Proof of (T2) for q.* For m ≥ 2, q_m = u_{m−1} ∗ τ with τ(v) = T(v)1{v≥1}, and u_{m−1} vanishes
at arguments ≤ 0, so Δ^r q_m(j) = Σ_{v≥1}T(v)Δ^r u_{m−1}(j−v). For m = 1, Δ^r q_1 = Δ^r T is one
term, of size O(f(j)) = o(A^{−r}). Fix v_0.
- **v ≤ v_0.** If m ∉ I_j(K), then m−1 ∉ I_{j−v}(K/2) for large j. So this part is at most
  μ·sup_{v≤v_0}Σ_{m′∉I_{j−v}(K/2)}|Δ^r u_{m′}(j−v)|, which is bounded by the u case.
- **v_0 < v ≤ j/2.** This part is at most (Σ_{v>v_0}T(v))·sup_{i≥j/2}Σ_{m′}|Δ^r u_{m′}(i)|
  ≤ (Σ_{v>v_0}T(v))·CA^{−r}, which is small when v_0 is large.
- **v > j/2.** Do not take absolute values inside the sum over v. For fixed m′, sum by parts r
  times in i = j − v ≤ j/2:
  Σ_{i<j/2}T(j−i)Δ^r u_{m′}(i) = (−1)^r Σ_{i} u_{m′}(i)·Δ^r_i[T(j−i)] + boundary terms.
  - The boundary terms are products T(j/2 + O(1))·|Δ^{r−1}u_{m′}(⌊j/2⌋ + O(1))|, and, for r = 2,
    also |ΔT(j/2 + O(1))|·u_{m′}(⌊j/2⌋ + O(1)).
  - By (LD), |Δ^r_i T(j−i)| ≤ Cf(j)j^{1−r} for i ≤ j/2 + 2.
  - Summing the absolute values over all m′, with Σ_{m′}u_{m′}(i) ≤ 1, gives
    C(j/2)f(j)j^{1−r} + CT(j)Σ_{m′}|Δ^{r−1}u_{m′}(⌊j/2⌋)| + C f(j)
    ≤ CT(j)j^{1−r} + CT(j)a(j)^{1−r} + Cf(j).
  - For r = 1 this is o(A^{−1}). For r = 2 it is o(A^{−2}), since T(j)a(j)² = o(j) and
    T(j)a(j) → 0.
- The kernel q_{m+1} = u_m ∗ τ is the same.

Altogether Σ_{m∉I_j(K)}|Δ^r q_m(j)| ≤ C(K^{1−α+δ} + e^{−cK} + Σ_{v>v_0}T(v))A^{−r} + o(A^{−r}).
Let v_0 → ∞.

*Proof of (T1).*
- **m ≥ m_ε.** a(m) ≥ a(m_ε) ≥ ca(N), so this is (F1). For q, use |Δ^r q_m| ≤ μ sup|Δ^r u_{m−1}|.
- **m < m_ε, u.** Here x − mμ ≥ x/2 ≥ max(K_1a(m), L_0), so Lemma 12c gives Cm f(x)/x^r.
- **m < m_ε, q.** Split Σ_v T(v)Δ^r u_{m−1}(x−v) at v = x/2.
  - For v ≤ x/2, Lemma 12c at level x − v ≥ x/2 gives at most μCm f(x)/x^r.
  - For v > x/2, the summation by parts above, applied to the single m′ = m−1, gives at most
    Σ_i u_{m−1}(i)|Δ^r T(x−i)| + boundary ≤ C f(x)x^{1−r} + CT(x)|Δ^{r−1}u_{m−1}(x/2)|.
  - The last term is at most CT(x)·m f(x)x^{1−r}·C for r = 2, by Lemma 12c, and at most CT(x)
    for r = 1. Both are within the stated bound, since T(x)·m ≤ CmT(x) ≤ C and T(x) ≤ Cxf(x).

*Proof of (T1w).* By `lem:small`, 𝗄′_m(x′) ≤ C(1 + m/a′(m))T′(N) for m < m_ε. Also T′(N) is at
most CN^{−α′+δ}, and a(N), a′(N) ≥ N^{1/2}. Using (T1):
- **u-kernel.** Σ_{m<εN}(m f(N)N^{−r})(1 + m/a′(m))T′(N) ≤ CN^{3−r}f(N)T′(N)/a′(N)
  = CN^{2−r}T(N)T′(N)/a′(N).
  - For r = 1 this is N^{1−α−α′−1/α′+o(1)} = o(N^{−2/α_*}).
  - For r = 2 it is N^{−α−α′−1/α′+o(1)} = o(N^{−3/α_*}).
  - In both cases the exponents are compared using α, α′ > 1 > 1/α_*.
- **q-kernel.** Σ_m f(N)N^{1−r}(1 + m/N)(1 + m/a′(m))T′(N) ≤ CN^{2−r}T(N)T′(N)/a′(N). This is
  the same bound.
- **Mixed products (r = 2).** A u-kernel difference times a q-kernel difference gives
  Σ_{m<εN}(m f(N)/N)·f(N) ≤ CNf(N)² = CT(N)²/N = o(N^{−3/α_*}).
- B_N ≍ N^{1/α_*} up to slowly varying factors, which are absorbed by the o(·). ∎

**Correction to 04.** The first bullet of (T1) in 04 reads "Σ_{m<εN}|Δ^r𝗄_m(j)|·𝗄′_m ≤ o(…) for
any weights 𝗄′_m ≤ 1". That is false as stated: with weights equal to 1, the u-kernel sum is
about T(N)N^{1−r}, which is not o(B_N^{−1−r}) for α ≤ √2. The correct statement is (T1w), with
the weights given by the other kernel at a level of order N. That is what the proof of
Theorem 14 uses, so Theorem 14 stands.

**How Theorem 14 uses Lemma 12** (this replaces the last bullets of its proof in 04).
- **Difference on the τ factor, weights from the τ̄ factor.** For m ≥ m_ε, (T1) and
  Σ_{m∉I}𝗄^τ̄_m ≤ η(K) + o(1) give O(η(K))B_N^{−1−r}. For m < m_ε, (T1w) gives o(B_N^{−1−r}).
- **Difference on the τ̄ factor, weights from the τ factor.** By `eq:bulk-factor`, 𝗄^τ_m ≤ C/B_N.
  Then (T2) at level k_τ̄ gives O(ε_r(K))B_N^{−1}b_{τ̄,N}^{−r}, which is O(ε_r(K))B_N^{−1−r} by
  (EQ).
- **Mixed (r = 2).** For m ≥ m_ε, combine (T1) with (T2) for r = 1. For m < m_ε use (T1w).

**Numerical check** (`py -I check05_tails.py`). For the zeta law (α = 3/2), the quantity
A^r Σ_{m∉I_j(K)}|Δ^r𝗄_m(j)| at K = 2, 4, 8 and 16 is:
- u_m, r = 1: 0.117, 0.077, 0.0024, 0.0001 (j = 10³);
- u_m, r = 2: 0.088, 0.041, 0.0020, 0.0000;
- q_m, r = 1: 0.218, 0.141, 0.0057, 0.0005;
- q_m, r = 2: 0.157, 0.074, 0.0037, 0.0001.

At j = 250 and 500 the values are of the same size, without growth in j. They decrease in K, as
(T2) says.

## 2. The bell-shape input, checked against the full text

**Source.** M. Kwaśnicki, *A new class of bell-shaped functions*, arXiv:1710.11023v3 (27 Nov 2018),
full text. The journal version was not compared. The brief cites it as Trans. Amer. Math. Soc.
(2020), and the arXiv text carries no journal reference.

**What it says.**
- **§2, sign changes.** "We say that a function f : ℝ → ℝ changes its sign exactly n times if
  n + 1 is the maximal length m of a strictly increasing sequence x_1, …, x_m such that
  f(x_j)f(x_{j+1}) < 0." A zero at which f does not change sign is therefore not counted, and not
  excluded.
- **Definition 2.1.** "A smooth function f : ℝ → ℝ is said to be strictly bell-shaped if for every
  n = 0, 1, 2, … the n-th derivative f^{(n)} of f converges to zero at ±∞ and f^{(n)} changes its
  sign exactly n times."
- **Weakly bell-shaped** means that f ∗ G_t is strictly bell-shaped for every t > 0. A smooth
  weakly bell-shaped f is strictly bell-shaped (§2, the paragraph after Definition 2.1).
- **Corollary 1.3.** "All stable distributions on ℝ have bell-shaped density functions."
  - There is no restriction on the index or the skewness.
  - The introduction notes that the one-sided case was due to T. Simon, and that the earlier
    claim of [6] had a gap, which this paper closes.
  - Theorem 1.1, of which the corollary is a case, says "f is weakly bell-shaped. If in addition
    f is smooth, then f is bell-shaped". Stable densities are smooth, so Corollary 1.3 gives
    strict bell shape in the sense of Definition 2.1.

**The laws that arise.**
- Under (EQ), α_+ = α_− = α ∈ (1,2), and W_θ = (1−p)θ_+Z_+ − pθ_−Z_− is a positive combination
  of two independent strictly α-stable variables, so it is strictly α-stable.
- Its skewness is β = [((1−p)θ_+)^α − (pθ_−)^α]/[((1−p)θ_+)^α + (pθ_−)^α] ∈ [−1, 1], with the
  ends attained only when some θ_σ = 0.
- It is nondegenerate, since max θ_σ = 1.
- Without (EQ), the limit points θ ∈ {(1,0), (0,1)} give totally skewed α_σ-stable laws.
- Every one of these laws is covered by Corollary 1.3. For α > 1 the density is positive on ℝ
  and extends to an entire function (04, Lemma 13(a)).

**What is used, and the missing step.** The definition alone does not give h'' < 0 at the mode,
because h' could have a zero without a change of sign. Analyticity supplies the missing step.

**Lemma 16.** Let f be real-analytic, not identically zero, and strictly bell-shaped. Then for
every n, f^{(n)} has exactly n zeros, and all of them are simple. In particular f′ has a single
zero x_0, the mode, with f″(x_0) < 0, and f′ ≠ 0 elsewhere.

*Proof.* Let g = f^{(n)}. It is analytic and not identically zero, so its zeros are isolated and
of finite order. Say g has D distinct zeros. Of these, S change the sign of g (odd order) and T
do not (even order), so S = n and D = n + T.

**g′ changes sign at least D + 1 + T times:**
- once in each of the D − 1 bounded gaps between consecutive zeros, since g has one sign there
  and g ~ c(x−a)^k at each end, so g′ has opposite signs near the two ends;
- at least once in each of the two unbounded intervals, since g → 0 at ±∞ and g ≠ 0 there;
- once at each zero of g of even order, where g′ has a zero of odd order.

These sign changes occur at distinct points. Since g′ = f^{(n+1)} changes sign exactly n + 1 times,
n + 1 ≥ n + 1 + 2T, so T = 0.

**All zeros are simple.** Now T = 0 holds for every n. So every zero of every derivative changes
sign, D = n, and every zero has odd order k. If some zero a of g had order k ≥ 3, then a would be
a zero of g′ of even order k − 1 ≥ 2 without a change of sign. That contradicts T = 0 for n + 1.

**The mode.** For n = 1, f′ has exactly one zero, and it is simple. f > 0 tends to 0 at ±∞, so
the zero is the maximum, and f″(x_0) < 0. ∎

This replaces the argument of 04, Lemma 13(c), which reached the same conclusion through a count
of the extrema of h″. The uniform version, 04 Lemma 13(d), follows as stated: h_θ is continuous
in C², x_θ is continuous by the implicit function theorem (h_θ″(x_θ) < 0), and Θ_{θ_0} is
compact.

**Verdict.** Kwaśnicki's Corollary 1.3 plus analyticity give exactly what Theorem 14 and
Corollary 15 use, for every stable law that arises, at every skewness in [−1, 1]. Nothing is
missing. Unimodality (Yamazato) would not suffice; the higher-derivative sign counts are what
make Lemma 16 work.

## 3. Can (EQ) be weakened?

- **T_+/T_− → c > 0 is stronger than (EQ).** (EQ) asks only that T_+/T_− stay in a compact subset
  of (0, ∞).
- **(EQ) is a statement about scales.** It is equivalent to inf_N min_σ θ_{σ,N} > 0.
  - Comparable θ's mean a_+(t) ≍ a_−(t) for large t.
  - Inverting through tT_σ(a_σ(t)) → 1, with Potter's bounds, gives T_+ ≍ T_−.
- **(EQ) is used only at scale N.**
  - In the bulk (Theorem 14), only b_{τ̄,N} ≍ B_N enters.
  - In Theorem 10, the bad indices exist only when j ≥ εN, since m ≤ j + 1 and
    mμ_− − j ≥ μ_−L/(2μ_+) force j(μ_− − 1) + μ_− ≥ μ_−L/(2μ_+), which fails for j ≤ εN. There,
    a_±(j) ≍ a_±(N) by regular variation.
  - Steps (b), the copies and the layer do not use (EQ).
- **Corollary 17.** Assume the hypotheses of Theorem 1 with (EQ) replaced by α_+ = α_−, and fix
  θ_0 > 0. Then there is N_0 such that, for every N ≥ N_0 with min_σ θ_{σ,N} ≥ θ_0, the sign
  pattern of Theorem 1 holds and P_N has exactly M_+ + M_− + 1 modes. The constants depend on θ_0
  through the compactness in Lemma 13(d) and through the bad-index bound.
- **Example.** Equal indices with T_+/T_− oscillating between 0 and ∞ along a sparse sequence of
  scales give the exact count on the N where the scales are comparable. On the other N the window
  of `thm:window` appears, which is the unequal-scale problem, not attempted here.
- For α_+ ≠ α_−, θ_N tends to the boundary and Corollary 17 is empty. That case remains Theorem 1′.

## 4. Status after this round

| Claim | Status |
|---|---|
| Lemma 12a (pointwise bound, total variation) | proved |
| Lemma 12c ((D1′), second differences in the big-jump range) | proved, by the proof of Lemma 8 with the changes stated |
| Lemma 12 ((T1), (T1w), (T2)) | proved; the (T1) bullet of 04 is corrected to (T1w) |
| Theorem 14, Corollary 15 | proved under (EQ) (or along N with θ ≥ θ_0) |
| Bell-shape input | checked against Kwaśnicki's Definition 2.1 and Corollary 1.3 (arXiv v3); Lemma 16 supplies simple zeros by analyticity |
| **Theorem 1 of 04** | **proved, modulo audit**; (EQ) may be replaced by "min_σ θ_{σ,N} ≥ θ_0" along the N considered (Corollary 17) |
| Unequal scales (bulk with θ → 0, F's window) | open, not attempted |

**Files added:** `05_report.md`, `check05_tails.py`.
