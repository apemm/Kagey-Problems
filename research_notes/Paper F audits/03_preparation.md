# Paper F, Section 5 (Preparation): referee audit

Scope: `sec_preparation.tex` in full. I read it against the macros, `sec_setting.tex` (definitions, Proposition prop:first-run, Lemma lem:green, kernels K^sigma_m, the kernel kappa in eq:kappa), the statements of Theorem thm:bulk and Theorem thm:bigjump, and Theorem thm:inverse(b). I took Theorems thm:bulk and thm:bigjump as given. Where the preparation proofs use them, I checked each citation against the statement as written.

Scripts are in `scripts/preparation/` of this folder (`bl.py`, `test1.py`, `test2.py`, `test3.py`). The run recursion is copied from `certify_atlas.py` and cut down to at most J minus slots.

---

## 0. Summary

| # | Severity | Where | Defect |
|---|---|---|---|
| 1 | **Breaks the statement** | Thm thm:preparation(c); Lemma lem:unif-bigjump(ii); Cor cor:stationary(b) | The zone is written `pN + K B_N <= k`. Theorem thm:bigjump(b) proves it only on `pN + K lambda_N B_N <= k`. Remark rem:theta shows that without `lambda_N` the claim is false whenever `theta_{+,N} -> 0` along a subsequence (for example `alpha_+ > alpha_-`). That includes the fresh preparation itself. |
| 2 | **Breaks a proof** (once fix 1 is made) | Thm (c), "window condition sufficient under (LR) for both signs" | The tail blocks `|i| > R` use Lemma lem:unif-bigjump at both ends. With the correct zone, the blocks with `R < |i| <~ lambda B_N` (lambda the factor for the relevant end) are not covered. One of `lambda_{+,N}`, `lambda_{-,N}` is unbounded whenever `alpha_+ != alpha_-`. A repair exists through Lemma lem:no-big-run (sketch in Section 4.6). |
| 3 | Fixable in one line | Lemma lem:unif-bigjump(ii) vs Step 3 of the proof of (c) | The lemma compares with `G^{(sigma_0)}_n` of eq:G, which has the exact coefficient `gamma`. Step 3 then writes the kernels with the limit coefficient `(n - L)/mu_-`. The fix is to cite the last clause of thm:bigjump(b), the additive form with `gamma` replaced by `(N - L_k)/mu_-`. |
| 4 | Cosmetic | Lemma lem:unif-bigjump(i), proof | It bounds the first term as if the coefficient were `(n - L)/mu_-`. With `gamma`, use `gamma(j) <= (1 + mu_+) j <= (1 + mu_+) n`. |
| 5 | Cosmetic / consistency | Thm thm:inverse(b) | The second hypothesis, `L^+_N(j)/(B_N T_+(N)) -> 0`, follows from the first: `Q_+/T_+ -> q < infinity` forces `nu_+ = o(T_+)`. |
| 6 | Cosmetic | Rem rem:rho-diagram(ii) | The big-jump half of (ii) needs (LR) for the sign in question. The remark does not say so. |
| 7 | Cosmetic | Text after Thm (c)/(d), Rem rem:kappa-prep, section intro | The claim "(c) contains (d)" needs a one-line identification of `Psi_N` with `B_N^{-1} L^+_N`. The kappa-prep "exactly when" needs `pi_- > 0` to be meaningful. The intro sentence about the big-jump zone overstates the case: interior zones see window averages, not atoms. |

Everything else checks out: (a), (b), (d), the decomposition and whole-zone criteria in (c) once fixes 1 and 3 are made, the regular case, the interior necessity, Cor cor:stationary (a) and (c), Cor cor:no-trim, and Rem rem:rho-diagram. The exact small cases and the published numbers agree with the theorem (Section 6).

---

## 1. Does thm:bigjump match what Section 5 uses?

The section uses three things from thm:bigjump.

* **(a), fixed `j`.** Used in the proof of (d) at horizons `N - d` with `d <= j` (fresh plus) and with `d <= J` (fresh minus). The statement matches the use. Part (a) needs only (RV) for the plus sign, so (d) needs only (RV) and (SPAN), as claimed.
* **(b), ratio form.** Lemma lem:unif-bigjump(ii) quotes it as: *"there are K_0 and n_0 with `|F/G - 1| <= eps/C_3` for `n >= n_0` and `pn + K_0 B_n <= k <= n`."* **The statement of thm:bigjump(b) has `K lambda_N B_N`, not `K B_N`.** This is gap 1.
* **(b), additive form with the limit coefficient.** Step 3 of the proof of (c) uses kernels with `(n - L)/mu_-`. That is the last clause of thm:bigjump(b), but the lemma it cites is stated for `G^{(sigma_0)}_n` with `gamma`. This is gap 3.

thm:bigjump(b) is now stated additively as well (size function `\hat G_N = (N/L_k) T_+(\lfloor L_k \rfloor)`, the same `\widehat G_N` as eq:Psi). The additive form is what (c) needs, and with the limit coefficient it matches `G^\nu_N` exactly. So the only real mismatch is the zone.

---

## 2. Part (a): the exact defect

The decomposition is checked line by line.

* **`E_3` (late delays, `N/2 < d < N`).** With `m = N - d` this is literally `L^+_N(N - k) + L^-_N(k)`. For sign plus: `F^-_{N-d}(k - d) = K^-_{N-d}(N - k)`. For sign minus: `F^+_{N-d}(k) = K^+_{N-d}(k)`. Both identifications are correct. When `N` is even, `d = N/2` falls in `E_2` and `m = N/2` is excluded from eq:defect (`m < N/2`), so the split is consistent.
* **`E_2` (`J < d <= N/2`).** Horizon at least `N/2`, Thm bulk(b), and `B_N / B_{\lceil N/2 \rceil} <= C` give `E_2 <= C C_0 P(D > J)` uniformly in `k`. Correct.
* **`E_1` (`d <= J`).** I rechecked the shift. `y_k = (k - d - pn)/B_n = (k - pN - (1 - p) d)/B_n` for the minus-run case, and `pd` in place of `-(1 - p) d` for the plus case. The two-region argument works: on `|x| <= R` it uses the common Lipschitz constant and `||h_n - h_N|| -> 0`, and on `|x| > R` it uses `tau_infty(R/2)`. Summing over the finitely many `d <= J` gives `P(D <= J) h_N`.
* **Collecting.** `e_N = (E_1 - P(D <= J) h_N) + E_2 - P(D > J) h_N`, so the bound `(sup H + C C_0) P(D > J)` is right, and it is uniform in `0 <= k <= N`.

Lemma lem:prep-profile, all four parts, is sound. (iv) is the only nontrivial one. The interval covering, the `3R` count for `B_n >= 1, R >= 1`, monotonicity in `R`, and the finitely many small `n` are all handled.

**Verdict (a): sound.**

---

## 3. Part (b): the criteria and the error formulas

* **Disjoint supports.** `L^+_N(N - k) != 0` forces `k > N/2` and `L^-_N(k) != 0` forces `k < N/2`. So on `1 <= k < N` the sum of the defects is pointwise their maximum, and the sup is `max(Delta_+, Delta_-)`. Correct.
* **Interior error.** This follows from (a) and `| sup|f + g| - sup|f| | <= sup|g|` with `f >= 0`. Correct.
* **Whole-row error.** At `k = N`: `L^+_N(0) = L^-_N(N) = 0` and `x_{N,N} = (1 - p) N / B_N -> infinity`, so `h_N -> 0` by `tau_infty`. Same at `k = 0`. Correct.
* **Lower bound, `Delta_+ >= B_N nu_+(N - 1)`.** This is the term `m = 1, b = 1`, with `K^-_1(1) = 1`. It is the defect form of `P_N(N - 1) >= nu_+(N - 1)`, together with the vanishing of the profile at `x_{N,N-1}`. Correct. The converse then uses `B_{N-1} <= B_N` (monotone), and that is enough.
* **Upper bound, eq:defect-upper.** Green's identity and `u_- <= 1` give it. Correct.
* **Whole-row criterion.** `B_n nu <= B_n Q` gives the implication between the two criteria. Correct.
* **Fixed macroscopic interior.** Nonzero terms have `m >= N - k >= eps N`, so `K <= C_0 / B_{eps N}` and the defect is at most `C_0 (B_N / B_{eps N}) Q_+(\lceil N/2 \rceil) -> 0`. Correct.

**Verdict (b): sound.**

---

## 4. Part (c): the big-jump zone

### 4.1 Gap 1: the zone must carry `lambda_N` (breaks the statement)

Let `theta_{+,N} -> 0` along a subsequence. This happens whenever `alpha_+ > alpha_-`, and it can happen with equal indices. Take the **fresh plus preparation** (`nu_+ = f_+`, `nu_- = 0`) and `k = \lceil pN + K B_N \rceil` with `K` fixed.

* By Thm bulk(c) and Lemma lem:profile, `B_N P_N(k) >= c > 0`.
* `B_N \widehat G_N(k) = (N B_N / L_k) T_+(\lfloor L_k \rfloor) <= ((1 - p)/K) N T_+(\lfloor L_k \rfloor)`. By eq:NT-bounds and `L_k >= K b_{+,N} / theta_{+,N}`, this tends to `0`. This is exactly the computation of Remark rem:theta.
* `G^\nu_N <= C \widehat G_N` (Lemma lem:unif-bigjump(i)). Also `Psi_N <= (1 + mu_+) sup_{d >= L/2} f_+(d) = o(T_+(L)) = o(\widehat G_N)`.

Hence `|P_N - G^\nu_N - Psi_N| / \widehat G_N -> infinity` for every fixed `K`. The display in (c) is false as written. The same example makes Lemma lem:unif-bigjump(ii) false, and Cor cor:stationary(b) false (the stationary preparation satisfies the bulk criterion, so `B_N P_N(k) >= c` there too, while `B_N G^st_N(k) -> 0`).

**Fix.** Replace `pN + K B_N` by `pN + K lambda_N B_N` in (c), in Lemma lem:unif-bigjump(ii), and in Cor cor:stationary(b). At the minus end use `lambda_{-,N} = 1 + log(1/theta_{-,N})`. The proofs then go through unchanged in substance:

* For `n` in `[pN, N]`, `B_n / b_{+,n}` is a ratio of regularly varying functions. By the uniform convergence theorem, `lambda_n = lambda_N + o(1)` uniformly. So in Step 1, `k - pn >= K lambda_N B_N >= (K/2) lambda_n B_n` for large `N`. The same holds for `(k - d) - pn >= K lambda_N B_N / 2` when `d < L/2`.
* The whole-zone criterion, the regular case (`K >= R(1 - p)/delta + 1`) and the interior-zone statements involve bins with `k - pN` of order `N`, or they take `K` large anyway. So they are unaffected.
* The fixed-`v` limit in Cor cor:stationary(b) is unaffected, since `k - pN ~ (v - p) N`.

When `b_{+,N} = B_N` (for instance `alpha_+ < alpha_-`), `lambda_N = 1` and the text as written is correct.

### 4.2 The decomposition (Steps 1 to 4), assuming fixes 1 and 3

* **Step 1.**
  * `L^{(N-d)}_k = L + pd/(1 - p)`, `(N - d) - L' = (j - d)/(1 - p)`, `L^{(N-d)}_{k-d} = L - d`, and `(N - d) - (L - d) = N - L`. All verified.
  * The bound `\widehat G_{N-d}(k) <= \widehat G_N(k)` holds because `T_+` is nonincreasing and `L' >= L`.
  * The bound `\widehat G_{N-d}(k - d) <= C_4 \widehat G_N(k)` for `d < L/2` follows from `\lfloor L - d \rfloor >= \lfloor L/2 \rfloor` and Potter's bounds.
* **Step 2.** `S_2` needs `d <= j` (otherwise the terms vanish), and then `n = N - d >= k > pN >= n_0`. Correct.
* **Step 3.** The two kernel formulas are right with the limit coefficient (gap 3). Summing gives:
  * interior coefficient `(pi_+ + pi_-)(N - L)/mu_-`, up to `P(D > J)`;
  * boundary coefficient `T_+(\lfloor L \rfloor)[pi_+ u_-(j) 1_{j>=1} + sum_{d<=j} nu_-(d) u_-(j - d)] = T_+(\lfloor L \rfloor) kappa_+(j)`.

  This is exactly eq:kappa-prep and eq:G-prep. The `j < J` subcase (interior term `<= C(J/N) \widehat G`) and the `eta_N` uniformity (`f_+` eventually positive by (LR)) are fine.
* **Step 4.** `J/L <= (1 - p) J / (K B_N)`. The order of limits (`N`, then `J`, then `eps`) is correct.

**Gap 3, one-line fix.** As stated, Lemma lem:unif-bigjump(ii) bounds `|F - G^{(sigma_0)}_n|` with `G` from eq:G, whose first coefficient is `gamma^{(sigma_0)}_+(n - k)`. Step 3 replaces it by `(n - L)/mu_-` without comment. Either state (ii) with the limit coefficient and prove it from the last clause of thm:bigjump(b), or add the step `|gamma(j) - js/mu_-^2| f_+(\hat L) = o(\widehat G)`. The second route is already proved in Section 4, in the proof of (b).

### 4.3 Whole-zone criterion `nu_+ = o(T_+)`

* **Sufficiency (eq:Psi-upper).** Distinct `d` give distinct `m = N - d`. Green's identity gives total mass `1 + mu_+ u_-(j) <= 1 + mu_+`. Then `o(T_+(L/2)) = o(T_+(L)) <= o(\widehat G)` because `L >= K B_N -> infinity`. Correct.
* **Necessity.** `k = N - 1` lies in the zone for every `K` (with or without `lambda_N`, since `lambda_N B_N = o(N)`). `d = N - 1 >= L_k/2`, `F^-_1(0) = 1`, and `\widehat G_N(N - 1) <= C T_+(N)`. Correct.

### 4.4 The regular case (R nu)

* `V = {|d - L_k| <= R B_N}`, and `|m - j/(1 - p)| = |d - L_k|` because `N - L_k = j/(1 - p)`.
* Terms with `d >= N` have `m <= 0` and contribute nothing, which is consistent with Lemma lem:green-conc summing over `m >= 1`.
* The off-window part is at most `eps sup_{d >= L/2} nu_+ <= eps C_nu nu_+(\lfloor L \rfloor)`, by the first half of (R nu).
* Lemma lem:green-conc itself is sound. `xi_j <= X_r` with `X_r` independent of `(r, tau_j)`. The two deviation events are rewritten through `A_{m_i}`. `m_i <= c_0 N` and `B_{m_i} <= c_1 B_N`. The result is uniform in `1 <= j <= N`.

**Verdict on this piece: sound.** The error term relative to `\widehat G + nu_+(\lfloor L \rfloor)` is what the statement says.

### 4.5 Interior zones: sufficiency of `nu = o(T)` and necessity of the window condition

* **Sufficiency of `nu = o(T)`.** This is eq:Psi-upper. Correct.
* **Necessity of the window condition.** Take `N = 2n` and `|L_k - n| <= 1/(1 - p)`, so `k` is in `Z^{1/4}`.
  * For `|d - n| <= B_n`: `m` lies in `[N/4, 3N/4]`, and `(1 - p) m - j = (1 - p)(L_k - d)` is `O(B_m)`.
  * Bulk(c) and the uniform positivity of `h` on compacts give `B_m K^-_m(j) >= c_3`.
  * Hence `Psi >= (c_3/C) W_n`.

  Correct. This does not need `lambda_N`.

### 4.6 Gap 2: sufficiency of the window condition under (LR) for both signs

The argument as written is correct as far as it goes:

* blocks of width `B_N`, each covered by `C_eps` windows;
* the near blocks `|i| <= R` contribute `O(W̄_N)`;
* the far blocks use Lemma lem:unif-bigjump at the plus end (excess) and the minus end (deficit), with `L' = y/(1 - p)`, `L'' = y/p`, `c = (1/2) min(1, (1 - p)/p)`, Potter's bounds, and `N T_sigma(B_N) <= N T_sigma(b_{sigma,N}) -> s`.

After fix 1, however, Lemma lem:unif-bigjump(ii) needs `y >= K_0 lambda_{±,m} B_m`. When `alpha_+ != alpha_-`, one of `lambda_{+,N}`, `lambda_{-,N}` grows like `log N`. The blocks with `R < |i| <~ lambda B_N` on that side are then covered by nothing in the proof. The bulk bound `B_m K^-_m(j) <= h + eta_N` costs `eta_N lambda_N W̄_N`, and Thm bulk(a) gives no rate for `eta_N`. So the claim is not proved as written.

**Repair (sketch; I checked the exponents).** Skip Lemma lem:unif-bigjump in the far blocks. For a fresh walk at horizon `m` and a plus count with excess `L >= C_0 B_m`, combine eq:giant-split with eq:giant-crude and Lemma lem:no-big-run:

```
F_m(count) <= C (m T_+(L))^r / b_{+,m} + C e^{-cL/b_{-,m}} / b_{-,m} + C e^{-m^c}
              + kappa T_+(eta L) + gamma f*_+(eta L).
```

This holds for `L >= C_0 B_m` with no `lambda`. With block mass `<= C_eps B_N W̄_N` and `L ≍ |i| B_N`:

* **First term.** `r >= 2` and eq:NT-bounds give `B_N (m T_+(|i| B_N))^r / b_+ <= C (B_N / b_+)^{-alpha_+} |i|^{-alpha_+ - 1}`. This sums over `i`.
* **Second term.** `B_N e^{-c |i| B_N / b_-} / b_- `, summed over `i >= 1`, is at most `(B_N/b_-) / (e^{c B_N / b_-} - 1) <= 1/c`.
* **Third term.** At most `N` blocks times `B_N e^{-N^c}`, which tends to `0`.
* **Last two terms.** These are the `\widehat G`-type terms. The paper already sums them with Potter's bounds.

The deficit side is the same with the signs exchanged. It uses the minus-end version of Lemma lem:no-big-run and (LR) for the minus sign to bound `f*_-`. The result is again `Psi_N <= C_{eps,R} W̄_N`.

Two alternatives: write this argument out, or restrict the claim to the case where `lambda_{+,N}` and `lambda_{-,N}` are both bounded.

### 4.7 The "gap is real" example

`nu_+(n_i) = T_+(n_i)` on a sequence sparse enough that each window holds at most one atom gives `W_n <= C T_+(n) / B_n = o(T_+(n))`. Then `P_{n_i + 1}(n_i) >= nu_+(n_i) F^-_1(0) = T_+(n_i)`. Correct. Its interior-invisibility half depends on 4.6.

**Verdict (c):** unsound as written (gap 1). After the `lambda_N` fix and the one-line fix 3, the decomposition, the whole-zone criterion, the regular case, interior sufficiency of `nu = o(T)`, and interior necessity of the window condition are all sound. The interior sufficiency of the window condition stays unproved until 4.6 is written out (or the claim is restricted).

---

## 5. Part (d), the boundary layer, and Remark rem:kappa-prep

### 5.1 Proof of (d)

* **First sum.** `d <= j`, and `F^+_{N-d}(N - j) / T_+(N - d) -> u_-(j - d)` by thm:bigjump(a) and eq:kappa. The term `d = j` is exact, since `F^+_{N-j}(N - j) = T_+(N - j)` and `u_-(0) = 1`.
* **Second sum.**
  * `d <= J`: limit `u_-(j) 1_{j>=1}`.
  * `J < d <= N/2`: bounded by `C C_j Q_+(J + 1) T_+(N)`. The bound "convergent hence bounded" is legitimate. Lemma lem:end-crude gives it directly and uniformly.
  * `d > N/2`: exactly `B_N^{-1} L^+_N(j)`.
* **Collecting.** Replacing `P(Sigma = +, D <= J)` by `pi_+` costs `Q_+(J + 1)`. The final bound `(1 + C C_j) Q_+(J + 1)` is right.

### 5.2 The criterion

* **Sufficiency.** `B_N^{-1} L^+_N(j) <= (1 + mu_+) sup_{d > N/2} nu_+(d) = o(T_+(N))`.
* **Necessity.** The term `m = j` gives `nu_+(N - j) K^-_j(j) = nu_+(N - j) T_-(j)`, with `T_-(j) > 0` under (RV). Correct.
* **(R nu) form.** Dominated convergence, with dominating weights `C K^-_m(j)` of total mass `C(1 + mu_+ u_-(j))`. Correct.

### 5.3 "(c) contains (d)"

At `k = N - j`:

* `G^\nu_N(N - j) = T_+(N) kappa_+(j) + O(j T_+(N)/N)`.
* `Psi_N(N - j) - B_N^{-1} L^+_N(j)` is the sum over `d` in `[L_k/2, N/2]`. That is at most `j/(2(1 - p)) + 1` values of `d`, each with `K^-_m(j) <= C_j T_+(m)` and `m ~ N/2`, so it is `o(T_+(N))`.

So the two expansions agree. One sentence in the text would make this explicit (cosmetic 7).

### 5.4 Remark rem:kappa-prep

* **The limit.** `kappa_+(j) -> (pi_+ + pi_-)/mu_-` by the renewal theorem and dominated convergence. Correct.
* **The generating-function criterion.** For `j >= 1`, `kappa_+(j) = pi_+ u_-(j) + [\hat nu_- U]_j`, and `\hat nu_- U` has no constant term. So `kappa_+ = u_-` on `j >= 1` iff `\hat nu_- U = pi_- (U - 1)`, iff `\hat nu_- = pi_- (1 - 1/U) = pi_- F`. Correct. When `pi_- = 0` the condition is automatic and "given that it is a minus run" is vacuous; say "`nu_- = pi_- f_-`" instead (cosmetic).
* **The length-2 example.** `kappa_+(j) = pi_+ u_-(j) + pi_- u_-(j - 2)` is correct, including `j = 1`. It differs from `u_-` because `f_- = delta_2` would violate (SPAN). The remark should say that it differs.

  Numerical check (zeta law with alpha = 1.5 for both signs, `pi_+ = 1/2`, `nu_+ = f_+/2`, `nu_-(2) = 1/2`):

  | `j` | `P_N(N - j)/T_+(N)` at N = 2400 | prediction | fresh `u_-(j)` |
  |---|---|---|---|
  | 1 | 0.37417 | 0.37272 | 0.74544 |
  | 2 | 0.84685 | 0.84373 | 0.68746 |
  | 3 | 0.70734 | 0.70198 | 0.65851 |
  | 4 | 0.67122 | 0.66394 | 0.64042 |
  | 5 | 0.65221 | 0.64313 | 0.62774 |

  The deviations at N = 1200 are about twice these. The limit is the prepared kernel, not the fresh one.

### 5.5 Consistency with Theorem thm:inverse(b)

thm:inverse(b) uses the same `kappa_+` formula and the same three-way split, and its conclusion is (d) with the defect assumed away. They are consistent. One observation (cosmetic 5): if `Q_+(N)/T_+(N) -> q < infinity`, then `nu_+(N) = Q_+(N) - Q_+(N + 1) = o(T_+(N))`, because `T_+(N + 1)/T_+(N) -> 1`. By eq:defect-upper the defect hypothesis `L^+_N(j)/(B_N T_+(N)) -> 0` is then automatic. The second hypothesis of thm:inverse(b) can be dropped, or kept with a remark that it is implied.

**Verdict (d): sound.** Rem rem:kappa-prep: sound, with the cosmetic notes above.

---

## 6. Smallest cases, recomputed from the definitions

Notation: `(f*T)(n) = sum_{a=1}^{n-1} f_+(a) T_+(n - a)`, `(f*f)(n) = sum_{a=1}^{n-1} f_+(a) f_+(n - a)`, and `(f*f*T)(n) = sum f_+(a) f_+(b) T_+(n - a - b)` over `a, b >= 1` with `n - a - b >= 1`. Every closed form below matched the run recursion to machine precision: N = 60 against `occupation` from `certify_atlas.py`, and N = 50 with unequal laws (alpha_+ = 1.5, alpha_- = 1.3) for the stationary start.

**Fresh plus start.**

* `P_N(N - 1) = f_-(1) (f*T)(N - 1) + f_+(N - 1)`.

  Since `(f*T)(n) ~ T_+(n)` and `f_+ = o(T_+)`, this gives `P_N(N - 1)/T_+(N) -> f_-(1) = u_-(1) = kappa_+(1)`. In the framework of (d) (`nu_+ = f_+`, `pi_+ = 1`), the defect is `B_N^{-1} L^+_N(1) = f_+(N - 1) + f_-(1) sum_{2 <= m < N/2} f_+(N - m) T_+(m - 1) = O(f_+(N)) = o(T_+(N))`, as (d) predicts. This is exactly the late-`d` part of the formula above.

* `P_N(N - 2) = f_-(2) (f*T)(N - 2) + f_-(1)^2 (f*f*T)(N - 2) + f_-(1) (f*f)(N - 2) + f_+(N - 2) T_-(2)`.

  The limit is `(f_-(2) + f_-(1)^2) T_+(N) = u_-(2) T_+(N)`. The last two terms are `O(f_+(N))`. This agrees with (d) and with thm:bigjump(a).

**Stationary start** (`nu_sigma = T_sigma / s`).

* `P_N(N - 1) = (2/s) T_+(N - 1) + (f_-(1)/s) sum_{d=1}^{N-2} T_+(d) T_+(N - 1 - d)`.

  The convolution is `~ 2 mu_+ T_+(N)`, so `P_N(N - 1)/T_+(N) -> (2/s)(1 + mu_+ u_-(1)) = kappa^st_+(1)`. The three readings in the text match the terms:
  * `nu_-(1) T_+(N - 1) = T_+/s` is the short first minus run;
  * the small-`d` part of the convolution is `p u_-(1)`;
  * `nu_+(N - 1)` plus the large-`d` part is `(1 + mu_+ u_-(1))/s`.

* `P_N(N - 2) = (1/s)[f_-(1)(f*T)(N - 2) + f_+(N - 2)] + (2 T_-(2)/s) T_+(N - 2) + sum_{d=1}^{N-3} (T_+(d)/s)[f_-(2) T_+(N - d - 2) + f_-(1)^2 (f*T)(N - d - 2) + f_-(1) f_+(N - d - 2)]`.

  The convolution asymptotics `(T*T) ~ 2 mu_+ T`, `(T*f*T) ~ 2 mu_+ T` and `(T*f) ~ T` give the limit `(1/s)[2 T_-(2) + 2 f_-(1) + 2 mu_+ (f_-(2) + f_-(1)^2)] = (2/s)(1 + mu_+ u_-(2)) = kappa^st_+(2)`, using `T_-(2) + f_-(1) = 1`.

**The numbers in the text after Cor cor:stationary.** Ratio of `P_N(N - j)/T_+(N)` to `kappa^st_+(j)`, zeta law with alpha = 1.5 for both signs:

| `j` | N = 1200 | N = 2400 |
|---|---|---|
| 1 | 1.00142 | 1.00071 |
| 2 | 1.00619 | 1.00309 |
| 5 | 1.01972 | 1.00980 |

These reproduce the stated `1.0007, 1.0031, 1.0098`, and each deviation halves from N = 1200 to N = 2400, as stated.

---

## 7. Corollary cor:stationary

* **Bulk criterion.** `B_n T_sigma(n)` is regularly varying with index `1/alpha_* - alpha_sigma < 0`. Correct. (The whole-row criterion fails, since `B_n Q_sigma(n)` has index `1/alpha_* + 1 - alpha_sigma`. The corollary rightly claims only the interior criterion.)
* **(a).** Karamata. Correct.
* **Renewal identity.** `sum_{a=0}^{j-1} u_-(a) T_-(j - a) = 1` (the last renewal before `j`), so `sum_d T_-(d) u_-(j - d) = 1`. With `pi_+ = mu_+/s = p`, this gives `kappa_+(j) = p u_-(j) + 1/s`. Correct.
* **(c).** (R nu) holds for `T_+/s`. Then `p u + 1/s + (1 + mu_+ u)/s = (2/s)(1 + mu_+ u_-(j))`. The limit as `j -> infinity` is `(2/s)(s/mu_-) = 2/mu_-`, which equals `I_+(1) + 1/mu_-`. `P_N(N)/T_+(N) = Q_+/T_+ -> infinity`. All correct.
* **(b).**
  * The regular form gives `G^\nu + (T_+(\lfloor L \rfloor)/s)(1 + mu_+ u_-(j)) = G^st`, and `nu_+(\lfloor L \rfloor) <= \widehat G` absorbs the enlarged error.
  * The lower bound `G^st >= c \widehat G` is correct in both regimes: `kappa^st >= 2/s` when `L > N/2`, and (LR) when `L <= N/2`.
  * The fixed-`v` limit `I_+(v) + ell^{-alpha_+}/mu_-` is correct.
  * The extra term is `T_+(\lfloor L \rfloor)/mu_-`, the complete initial plus run. The interpretation is correct.
  * **But the zone must be `pN + K lambda_N B_N <= k < N` (gap 1).**

**Verdict:** (a) and (c) sound. (b) sound once the `lambda_N` fix is made.

---

## 8. Corollary cor:no-trim

* `R(n) = o(n)`, `m(n) -> infinity`, `m(n) = o(n)`, and `B_{m(n)}/B_n -> 0` by Potter's bounds. All correct.
* The preparation is chosen once: the sequence `n_i` (with `n_{i+1} > 2 n_i`, `sum v_i <= 1/2`) is fixed before any horizon is considered. `Sigma = +` almost surely, the atoms are `v_i` at `n_i`, and the rest of the mass sits at `d = 1` (take `n_1 > 1`).
* The lower bound `B_{N_i} P_{N_i}(k_i) >= B_{N_i} v_i F^-_{m_i}(k'_i) >= c B_{N_i}/B_{n_i} >= c` is correct.
* `x_{N_i,k_i} >= ((1 - p) n_i - 1)/B_{2 n_i} -> infinity`. Correct.
* **The atom lands inside the retained interval.** `r_{N_i} <= R(n_i) = o(n_i) <= k_i`, and `N_i - k_i = m_i - \lfloor p m_i \rfloor >= (1 - p) m_i >= 4(R(n_i) + 1) > r_{N_i}`. Both checked.
* This is consistent with (b): `k_i/N_i -> 1`, so `k_i` leaves every macroscopic interior. The remark that `B_{n_i} nu_+(n_i) = B_{m_i} -> infinity` is correct.

**Verdict: sound.**

---

## 9. Remark rem:rho-diagram

* **Index arithmetic.** `nu` has index `-rho - 1`, `B nu` has index `1/alpha_* - rho - 1 < 0`, `B Q` has index `1/alpha_* - rho`, `nu/T` has index `alpha - 1 - rho`, and `Q/T` has index `alpha - rho`. All correct.
* **(R nu).** It follows from regular variation, through Potter's bounds and the uniform convergence theorem. Correct.
* **Placements.** Stationary: `rho = alpha - 1`, with local regularity by Karamata. Fresh: `rho = alpha`, with local regularity equal to (LR). Both correct.
* **Without the local regularity.** `Q(n + 1)/Q(n) -> 1` gives `nu = o(Q)`, and only that. Correct.
* **Missing hypothesis (cosmetic 6).** The big-jump half of (ii), and the "extra term dominates near the endpoint" claim, need (LR) for the sign in question. That is the hypothesis of (c), and the remark does not state it. The boundary-layer half (via (d)) needs only (RV) and (SPAN).

**Verdict: sound, with the hypothesis added.**

---

## 10. Verdicts

| Statement | Verdict | Remaining gap |
|---|---|---|
| Thm thm:preparation(a) | **Sound** | None |
| Thm thm:preparation(b) | **Sound** | None |
| Thm thm:preparation(c), decomposition and whole-zone criterion `nu_+ = o(T_+)` | **Unsound as written; sound with fixes 1 and 3** | The zone must be `pN + K lambda_N B_N <= k`. Use the additive limit-coefficient form of thm:bigjump(b) in Lemma lem:unif-bigjump(ii). |
| Thm (c), regular case (R nu) | Sound with fix 1 | None |
| Thm (c), interior: sufficiency of `nu = o(T)`, necessity of `W_n = o(T)` | Sound | None |
| Thm (c), interior: sufficiency of `W_n = o(T)` under (LR) for both signs | **Proof incomplete after fix 1** | The intermediate blocks `R < |i| <~ lambda B_N` at the end where `lambda` is unbounded. Repair through Lemma lem:no-big-run plus eq:giant-crude (Section 4.6), or restrict the claim to bounded `lambda_{+,N}` and `lambda_{-,N}`. |
| Thm (c), the "gap is real" example | Sound for the atom side; interior side depends on the row above | As in the row above |
| Thm thm:preparation(d) | **Sound** | None |
| Rem rem:kappa-prep (`nu_- = pi_- f_-` criterion, length-2 example) | Sound with cosmetic fixes | State that the example differs from `u_-`. Phrase the criterion as `nu_- = pi_- f_-`. |
| Lemma lem:prep-profile | Sound | None |
| Lemma lem:green-conc | Sound | None |
| Lemma lem:unif-bigjump | (i) sound (cosmetic 4); **(ii) false as stated** | Needs `K_0 lambda_n B_n` and the limit-coefficient kernel. |
| Cor cor:stationary | (a), (c) sound; (b) sound with fix 1 | The zone in (b) needs `lambda_N`. |
| Cor cor:no-trim | **Sound** | None |
| Rem rem:rho-diagram | Sound with listed fix | Add (LR) to the big-jump half of (ii). |
| Consistency with thm:inverse(b) | Consistent | The second hypothesis of thm:inverse(b) is implied by the first (cosmetic 5). |
