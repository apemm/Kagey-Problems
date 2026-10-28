# Audit of three lemmas in Paper G, `sec_tools.tex`

Date: 2026-10-28.
Files audited: `kagey-problems/problem131/paperG/sec_tools.tex`, with notation and hypotheses from `paperG/sec_setting.tex` and Lemma `lem:rv-facts` from `paperG/sec_appendix.tex`.
Taken as given: (R1) to (R4), Lemma `lem:cd` (i) to (v), Lemma `lem:sums`, Lemma `lem:key`.
Mode: adversarial, from the definitions. For each claim the critical step was re-derived before the author's argument was read. No file in `paperG` or `paperF` was changed.

## Verdicts

| Claim | Verdict | Smallest gap |
|---|---|---|
| Lemma `lem:onejump` | proved as written | none |
| Lemma `lem:fourier` (i), (ii), (iii) | proved as written | one false but unused sentence in (ii) (direction of an inequality); Potter exponent `delta` must be in `(0, alpha)`, not said |
| Lemma `lem:Q` (i), (ii), including the identification with `phi` | proved as written | in (ii) the one-jump lemma is invoked at `y = k - w` where only `mT(k-w) <= 2 epsilon` is known, so `varrho(epsilon,k)` must read `varrho(2 epsilon,k)`; the constant `3 varrho` is `4 varrho` under the stated bound `T(k-w)/T(k) <= 2`. Both are one-token repairs and change no limit. |

All three statements are true as stated under the stated hypotheses. No restriction of a statement was needed.

---

## 1. Lemma `lem:onejump` (one big jump)

### Claim card

- Objects: a law on `{1,2,...}` with tail `T(x) = P(X >= x)`, i.i.d. copies `X_1, X_2, ...`, `S_m = X_1 + ... + X_m`.
- Hypothesis: `T` regularly varying with index `-alpha`, `0 < alpha < 1`. Nothing else (no (SPAN), no (SRT)).
- Definition: for `epsilon > 0`, `x >= 1`,
  `varrho(epsilon, x) = sup { |P(S_m >= y)/(m T(y)) - 1| : y >= x/2, m >= 1, m T(y) <= epsilon }`.
- Conclusion: `lim_{epsilon -> 0} limsup_{x -> inf} varrho(epsilon, x) = 0`.
- Quantifiers: the sup is over all real `y >= x/2` and all integers `m >= 1` jointly with `m T(y) <= epsilon`; `varrho` is nondecreasing in `epsilon` and nonincreasing in `x`, so the double limit is well posed.

### Independent derivation of the critical step

The statement is the uniform one-big-jump asymptotic `P(S_m >= y) ~ m T(y)` on the region `m T(y) -> 0`, which for `alpha < 1` is exactly `y / a_m -> inf`. It is a known result (Denisov, Dieker and Shneer 2008 give the big-jump domain for regularly varying tails; the infinite-mean case has domain `{y >> a_m}`), so the statement is true. The decisive step is a decomposition of `{S_m >= y}` into "one summand near `y`", "two summands of size `delta y`", and "many small summands add to `eta y`", with the last controlled by a Chernoff bound for bounded summands whose mean is `O(delta y T(y))`.

### Check of the written proof

Lower bound. `P(S_m >= y) >= P(max X_i >= y) = 1 - (1 - T(y))^m >= m T(y) - binom(m,2) T(y)^2 >= m T(y)(1 - m T(y)/2) >= m T(y)(1 - epsilon/2)`. Bonferroni of second order, valid for every `m >= 1` and `p in [0,1]`. Correct.

Upper bound. Fix `0 < delta < eta < 1/2` with `eta/delta >= 2`. The four events are exhaustive on `{S_m >= y}`: if no summand is `>= (1-eta) y` and exactly one is `>= delta y`, then that one is `< (1-eta) y` and the remainder `W` satisfies `W >= y - (1-eta) y = eta y`; if none is `>= delta y` then `S_m = W >= y`. Checked.

- Event 1: `m T((1-eta) y)`. By (R1) with the fixed `lambda = 1-eta`, `T((1-eta) y)/T(y) -> (1-eta)^{-alpha}` as `y -> inf`; the `o(1)` depends only on `y >= x/2`, hence only on `x`, and not on `m`. Correct.
- Event 2: `binom(m,2) T(delta y)^2 <= m^2 T(delta y)^2 <= C_delta^2 m^2 T(y)^2 = C_delta^2 (m T(y)) m T(y) <= C_delta epsilon m T(y)`, using (R2) with `c = 1/delta`, which needs `y >= 1/delta`; true for large `x`. Correct.
- Chernoff bound. The truncated summands `Y_i = X_i 1{X_i < delta y}` lie in `[0, delta y)`, and for `0 <= Y <= L` convexity gives `e^{lambda Y} <= 1 + (e^{lambda L} - 1) Y/L`. With `E[X; X < delta y] <= C delta y T(delta y) <= C_delta delta y T(y)` (the first inequality is the one proved inside `lem:sums`(i), valid for all arguments `>= 1`; for `delta y < 1` the expectation is `0`), one gets `E e^{lambda W} <= exp( m (e^{lambda delta y} - 1) C_delta T(y) )`. With `B = C_delta delta m T(y) y` and `e^{lambda delta y} = z/B` (which needs `z >= B`; the text asks `z >= eB`, which is stronger and gives `lambda > 0`), the exponent is `-(z/(delta y)) log(z/B) + z/(delta y)`, so `P(W >= z) <= (eB/z)^{z/(delta y)}`. I re-derived this and it matches the display. At `z = eta y`: base `= (e C_delta delta/eta) m T(y) =: C_{delta,eta} m T(y)`, exponent `eta/delta >= 2`; the condition `z >= eB` is `m T(y) <= eta/(e C_delta delta)`, which holds once `epsilon` is small, and the base is `<= 1` once `C_{delta,eta} epsilon <= 1`. Then `(base)^{eta/delta} <= (base)^2 <= C_{delta,eta}^2 epsilon m T(y)`. Correct.
- Event 3: `<= sum_i P(X_i >= delta y) P(W_{m-1} >= eta y) = m T(delta y) P(W_{m-1} >= eta y)` by independence, and the Chernoff bound for `m-1` summands has a smaller base, so `P(W_{m-1} >= eta y) <= (C_{delta,eta} epsilon)^2`. Hence event 3 is `<= C_delta m T(y) C epsilon^2 <= C epsilon m T(y)`. Correct (and for `m = 1`, `W_0 = 0`).
- Event 4: `<= P(W >= y) <= P(W >= eta y)`. Correct.

Adding: `P(S_m >= y) <= m T(y) [ (1-eta)^{-alpha} + o(1) + C_{delta,eta} epsilon ]`. The order of limits is `x -> inf` (kills the `o(1)`, and makes all "for large `y`" thresholds hold), then `epsilon -> 0` (kills `C_{delta,eta} epsilon`, with `delta, eta` fixed, so the constant is fixed), then `eta -> 0` with `delta = eta/2`. Each constant depends only on the parameters fixed before it. The lower bound gives `-epsilon/2`. So `lim_eps limsup_x varrho = 0`.

Uniformity in `m` was checked at every step: no bound uses `m -> inf` or `m` bounded. Potter's bound (R2) is used only with the fixed ratios `1/delta` and at arguments `>= 1/delta`, which `x -> inf` supplies.

### Verdict

Proved as written. No gap. (Cosmetic: the text could say that `delta` is chosen as a function of `eta`, for example `delta = eta/2`, so that the final limit is a single limit in `eta`.)

---

## 2. Lemma `lem:fourier` (Fourier bounds)

### Claim card

- Objects: one sign, `alpha < 1`, `varphi(t) = E e^{itX}`, `a_m` the scale with `m T(a_m) -> 1`, `u_m` the law of `S_m`, and for `y >= 1` the defective law `V^{(y)}_m(x) = P(S_m = x, max_{i <= m} X_i < y)`.
- Hypotheses: (RV) with index in `(0,1)` and (SPAN) for this sign.
- Conclusions:
  (i) there is `c > 0` with `|varphi(t)| <= exp(-c T(1/|t|))` for `0 < |t| <= pi`;
  (ii) for all `m >= 1`, `y >= 1`, all `x`: `|V^{(y)}_m(x-1) - V^{(y)}_m(x)| <= C e^{C m T(y)} a_m^{-2}`; in particular `sup_x |u_m(x-1) - u_m(x)| <= C a_m^{-2}`, and `|u_m(x-1) - u_m(x)| <= C a_m^{-2} e^{-c m T(x)}` for all `m >= 1`, `x >= 1`;
  (iii) `sup_x |u_{m+1}(x) - u_m(x)| <= C/(m a_m)` for all `m >= 1`.
- Quantifiers: all constants depend only on the law. "For all `m >= 1`" includes small `m`, where `a_m` is bounded and the bounds are trivial.

### Independent derivation of the critical steps

(i) `1 - |varphi(t)|^2 = E[1 - cos(t(X - X'))]`, and the symmetrised second moment truncated at `1/|t|` is `>= c t^2 (1/|t|)^2 T(1/|t|) = c T(1/|t|)` by Karamata, `E[X^2; X <= w] ~ (alpha/(2-alpha)) w^2 T(w)`. (SPAN) gives `|varphi| < 1` on `(0, 2 pi)`: if `|varphi(t)| = 1` the support lies in `c + (2 pi/t) Z`, and the gcd `d` of the support differences is a positive integer multiple of `2 pi/t > 1`, so `d >= 2`, contradicting (SPAN). Compactness closes the gap on `[t_0, pi]`.

(ii) The Fourier transform of `V^{(y)}_m` is `varphi_y^m` with `varphi_y(t) = sum_{n < y} f(n) e^{itn}`, because `{max < y}` factorises over the summands. `|varphi_y| <= |varphi| + T(y)`. A difference in `x` costs a factor `|e^{it} - 1| <= |t|`, and `int |t| exp(-c m T(1/|t|)) dt` scales as `a_m^{-2}` by the substitution `t = s/a_m` and Potter's lower bound `m T(a_m/s) >= c s^{alpha - delta}` for `1 <= s <= a_m/x_0`.

(iii) `|varphi(t) - 1| <= E min(2, |t| X) <= 2 T(1/|t|) + |t| E[X; X < 1/|t|] <= C T(1/|t|)`, and `int T(1/t) exp(-c m T(1/t)) dt` scales as `1/(m a_m)`.

### Check of the written proof

(i) `1 - cos(theta) >= theta^2/4` on `|theta| <= 1`: true (`1 - cos theta >= theta^2/2 - theta^4/24 >= 11 theta^2/24`). Restricting to `X' = n_0` and `2 n_0 <= n <= 1/(2|t|)` gives `|n - n_0| <= n <= 1/|t|` and `(n - n_0)^2 >= n^2/4`, so the displayed lower bound holds. `sum_{n <= w} n^2 f(n) >= c w^2 T(w)` for `w >= w_0` by Karamata (Abel summation gives `~ (alpha/(2-alpha)) w^2 T(w)`), and `t^2 w^2 = 1/4` at `w = 1/(2|t|)`; `T(1/(2|t|)) >= T(1/|t|)` since `T` is nonincreasing. On `[t_0, pi]` the (SPAN) argument above is what "(SPAN) gives `|varphi(t)| < 1`" needs, and the text's `1 - c_0 <= e^{-c_0} <= e^{-c T(1/|t|)}` for `c <= c_0` uses `T <= 1`. Correct.

(ii) `|varphi_y| <= |varphi| + T(y) <= e^{-c T(1/|t|)} (1 + e^c T(y))`: the second step uses `e^{-c T(1/|t|)} >= e^{-c}`. Then `|varphi_y|^m <= e^{e^c m T(y)} e^{-c m T(1/|t|)}`, so the constant in the exponent is `C = e^c`, independent of `m, y`. Inversion formula and `|e^{it} - 1| <= |t|`: correct.

The integral. After `t = s/a_m`, `int_{-pi}^{pi} |t| e^{-c m T(1/|t|)} dt = (2/a_m^2) int_0^{pi a_m} s e^{-c m T(a_m/s)} ds`.
- `s <= 1`: the text says "`m T(a_m/s) >= m T(a_m) >= c`". This is false as written: for `s <= 1`, `a_m/s >= a_m` and `T` is nonincreasing, so `T(a_m/s) <= T(a_m)`. The sentence is however not used: the bound actually applied is `e^{-c m T(.)} <= 1`, giving `int_0^1 s ds = 1/2`, which is what the final display contains. Harmless; the sentence should be deleted or replaced by "the exponential is at most `1`".
- `1 <= s <= a_m/x_0`: Potter's lower bound `T(a_m/s)/T(a_m) >= A^{-1} s^{alpha - delta}` for `a_m/s >= x_0`, together with `inf_m m T(a_m) > 0` (`lem:rv-facts`(ii) and positivity), gives `m T(a_m/s) >= c s^{alpha - delta}`. This needs `0 < delta < alpha`, which the text does not say; with `delta >= alpha` the integral `int_1^inf s e^{-c s^{alpha - delta}} ds` diverges. The restriction is free, so this is a missing word, not a gap. Also needs `a_m >= x_0`, i.e. `m >= m_0`; for `m < m_0` the claim is trivial since `a_m` is bounded and the left side is `<= 1`.
- `|t| >= 1/x_0`: `T(1/|t|) >= T(x_0) > 0`, so the integrand is `<= pi e^{-c m T(x_0)} = pi e^{-c' m}`, and `e^{-c' m} <= C a_m^{-2}` because `a_m <= C m^{1/alpha + delta}` (Potter for `a`). Correct.
So `|V^{(y)}_m(x-1) - V^{(y)}_m(x)| <= C e^{C m T(y)} a_m^{-2}` for all `m >= 1`, `y >= 1`, `x`. The case `y = inf` gives `V = u_m` and `T(inf) = 0`. Correct.

Last claim of (ii). For `m >= 2`, `k = ceil(m/2)`, `u_m(x-1) - u_m(x) = sum_z u_{m-k}(z) [u_k(x-1-z) - u_k(x-z)]`; the bracket vanishes for `z >= x` because `u_k(j) = 0` for `j <= 0` when `k >= 1`, so `|.| <= sup_z |u_k(z-1) - u_k(z)| P(S_{m-k} <= x-1) <= C a_k^{-2} e^{-(m-k) T(x)}` by `lem:sums`(ii). The text uses `P(S_{m-k} <= x) <= e^{-(m-k) T(x+1)}`, also correct. Then `a_k >= c a_m` (Potter for `a`, `k >= m/2`), `m - k = floor(m/2) >= m/3`, and `T(x+1) >= c T(x)` for all `x >= 1` (by (R1) with `lambda = 1 + 1/x in [1,2]` for large `x`, and positivity for bounded `x`). The text writes "`(m-k) T(x+1) >= c m T(x)`" without proof; it is routine as just shown. For `m = 1` the claim is trivial. Correct.

(iii) `|varphi(t) - 1| <= 2 T(1/|t|) + |t| E[X; X < 1/|t|] <= C T(1/|t|)`: the second term uses `E[X; X < w] <= C w T(w)` for `w >= 1` and vanishes for `w < 1`. Correct. After `t = s/a_m`: `s <= 1` gives `T(a_m/s) <= T(a_m) <= C/m` (this time the direction is right); `1 <= s <= a_m/x_0` gives `T(a_m/s) <= C s^{alpha + delta} T(a_m) <= C s^{alpha + delta}/m` and the exponential `<= e^{-c s^{alpha - delta}}`, and `int_1^inf s^{alpha + delta} e^{-c s^{alpha - delta}} ds < inf` for `0 < delta < alpha`; `s >= a_m/x_0` gives `e^{-c' m}` on a range of length `<= pi a_m`, and `a_m e^{-c' m} <= C/m`. Total `<= a_m^{-1} [C/m + C/m + C a_m e^{-c' m}] <= C/(m a_m)`. Correct, for all `m >= 1` (small `m` trivial).

### Verdict

Proved as written, for (i), (ii) and (iii). Two expository defects, neither affecting the conclusion:
1. In (ii), "For `s <= 1`, `m T(a_m/s) >= m T(a_m) >= c`" has the inequality reversed and is unused; replace by "for `s <= 1` the exponential is at most `1`".
2. In (ii) and (iii) the Potter exponent `delta` must satisfy `0 < delta < alpha` for `int_1^inf s e^{-c s^{alpha - delta}} ds` to converge; say "fix `delta in (0, alpha)`".

---

## 3. Lemma `lem:Q` (the local inverse renewal count)

### Claim card

- Objects: one sign, `alpha < 1`; `q_{m+1}(k) = P(S_m < k <= S_{m+1}) = sum_{r < k} u_m(r) T(k - r)`; `Z` the positive stable variable with Levy tail `z^{-alpha}` (Laplace exponent `Gamma(1-alpha) lambda^alpha`), `E = Z^{-alpha}`, `phi` the density of `E`; `p_t(z) = t^{-1/alpha} g(z t^{-1/alpha})`.
- Hypotheses: (RV) with index in `(0,1)` and (SPAN).
- Conclusions:
  (i) `q_{m+1}(k) >= (1 - C m T(k)) T(k)` for all `m >= 0`, `k >= 1`;
  (ii) for every `K > 0`, `sup { |q_{m+1}(k)/T(k) - phi(m T(k))| : m >= 0, m T(k) <= K } -> 0` as `k -> inf`;
  and, inside the proof, the identification `phi(t) = int_0^1 p_t(x) (1-x)^{-alpha} dx` for `t > 0`.
- Quantifiers: in (ii) the sup is over all integers `m` from `0` up to `K/T(k)`, so it includes bounded `m` (where `a_m` is bounded) and `m -> inf` with `m T(k)` bounded away from `0`.

### Independent derivation of the critical steps

Identification. `P(E >= t) = P(Z <= t^{-1/alpha}) = P(t^{1/alpha} Z <= 1) = P(sigma_t <= 1)`, where `sigma` is the driftless subordinator with Levy measure `alpha r^{-alpha-1} dr`, so `sigma_t =_d t^{1/alpha} Z` with density `p_t`. For `tau = inf{s : sigma_s > 1}`, monotonicity and right continuity give `{tau > t} = {sigma_t <= 1}`, hence `tau =_d E`. The subordinator has no drift, so it crosses `1` by a jump a.s., and the compensation formula gives `P(tau in dt, sigma_{tau-} in dx) = dt P(sigma_t in dx) Pibar(1 - x)` for `x < 1`, with `Pibar(r) = r^{-alpha}`. Integrating out `x`: `phi(t) = int_0^1 p_t(x) (1-x)^{-alpha} dx`. Consistency: as `t -> 0` the integral tends to `1 = phi(0)`, matching `P(E <= epsilon) ~ epsilon`.

Numerical referee (script and output in this folder: `check_lemQ3.py`, `check_lemQ3_output.txt`; `g` computed from Zolotarev's integral representation, `phi` from the Mittag-Leffler series `phi(t) = sum_n (-1)^n Gamma(1-alpha)^{n+1} t^n /(n! Gamma(1 - alpha(n+1)))`):

| alpha | t | series `phi(t)` | `int_0^1 p_t (1-x)^{-alpha}` |
|---|---|---|---|
| 0.3 | 0.3 / 0.8 / 1.5 | 0.7843221967 / 0.4921516033 / 0.2293552168 | 0.7843221967 / 0.4921516033 / 0.2293552168 |
| 0.5 | 0.3 / 0.8 / 1.5 | 0.9317545711 / 0.6049225628 / 0.1708198362 (= `e^{-pi t^2/4}`) | same to 10 digits |
| 0.7 | 0.3 / 0.8 / 1.5 | 1.636453274 / 0.2838514865 / 1.667484554e-8 | 1.636453251 / 0.2838514755 / 1.667359267e-8 |

The identification is confirmed (the `alpha = 0.7` residual is quadrature error near `x = 1`).

Limit on `m T(k) in [epsilon, K]`. `q_{m+1}(k) = sum_{r < k} u_m(r) T(k-r)`; with `a_m/k -> t^{1/alpha}`, Gnedenko's theorem, and (R1), the sum over `r < (1-eta) k` is a Riemann sum for `T(k) int_0^{1-eta} p_t(z) (1-z)^{-alpha} dz`, and the sum over `r >= (1-eta) k` is `O(eta^{1-alpha}) T(k)` by `sup u_m <= C/a_m` and Karamata.

Limit on `m T(k) <= epsilon`. The lower bound (i) is immediate. The upper bound needs the contribution of `r` near `k` to be `o(1) T(k)`, which is where the uniform one-big-jump estimate (Lemma `lem:onejump`) and Lemma `lem:cd`(ii) enter: the window `S_m in [k-w, k)` has probability at most `m T(k) [C w/k + o(1)]` by the one-jump asymptotics, and at most `C w (m/a_m) T(k)` by the local large deviation bound.

Numerical referee of (ii) itself, for `f(n) = n^{-1-alpha}/zeta(1+alpha)` (same script), `sup_{0 <= m T(k) <= 2} |q_{m+1}(k)/T(k) - phi(m T(k))|`:

| alpha | k = 4000 | k = 16000 | k = 64000 |
|---|---|---|---|
| 0.3 | 0.0145 | 0.0094 | 0.0062 |
| 0.5 | 0.0041 | 0.0021 | 0.0010 |
| 0.7 | 0.119 | 0.083 | 0.057 |

The gap decreases with `k` in every case, at a rate consistent with `k^{-(1-alpha)}` (slow at `alpha = 0.7`, as expected). No counterexample.

### Check of the written proof

(i) `T(k - r) >= T(k)` for `0 <= r < k` since `T` is nonincreasing, so `q_{m+1}(k) >= T(k) P(S_m < k) = T(k)(1 - P(S_m >= k)) >= T(k)(1 - C m T(k))` by `lem:sums`(i); for `m = 0` the probability is `0`. Correct.

(ii), range `m T(k) in [epsilon, K]`.
- `m >= epsilon/T(k) -> inf` with `k`, so Gnedenko's `o(1)` (which is a sup over `x`) is uniform over this range. Correct.
- `a_m/k -> t^{1/alpha}` uniformly: here `m = t/T(k)` exactly, so `m = m_k(t) = floor(t/T(k))` and `lem:rv-facts`(iii) with `N = k` applies uniformly for `t in [epsilon, K]`. Correct.
- Error term: `sum_{r < (1-eta) k} a_m^{-1} o(1) T(k-r) <= o(1) (k/a_m) T(eta k) <= o(1) C_{epsilon,eta} T(k)`, since `k/a_m <= C_epsilon` on this range. Correct.
- Main term: the Riemann sum `T(k) (k/a_m) sum (1/k) g((k/a_m) z_r) (1 - z_r)^{-alpha}` over `z_r = r/k < 1-eta` converges to `T(k) int_0^{1-eta} t^{-1/alpha} g(z t^{-1/alpha}) (1-z)^{-alpha} dz`, uniformly in `t in [epsilon, K]`, because `(z, s) -> s g(s z)(1-z)^{-alpha}` is uniformly continuous on `[0, 1-eta] x [K^{-1/alpha}, epsilon^{-1/alpha}]` (`g` bounded, continuous, vanishing at infinity) and `k/a_m -> t^{-1/alpha}` uniformly. The text writes the limit with `w = z t^{-1/alpha}`; same integral. Correct.
- Tail `r >= (1-eta) k`: `(C/a_m) sum_{i <= eta k} T(i) <= C (k/a_m) eta T(eta k) <= C_epsilon eta^{1-alpha} T(k)` for large `k`, by (R3) and (R1). Correct.
- `eta -> 0`: `int_0^{1-eta} -> int_0^1`, the integrand being `<= C epsilon^{-1/alpha} (1-z)^{-alpha}`, integrable. Correct.
- Identification with `phi`: checked above. The citation of Bertoin, Proposition III.2, is to the potential-measure form `P(sigma_{tau-} in dx, sigma_tau in dy) = U(dx) Pi(dy - x)`; the time-resolved density used here is the compensation formula itself (the text says "the compensation formula", which is the right tool). The step `{tau > t} = {sigma_t <= 1}` and `P(sigma_t = 1) = 0` are fine. Correct.

(ii), range `m T(k) <= epsilon`. The lower bound from (i) and `phi(t) = 1 + O(t)` (`phi` is entire; `phi'(0) = -Gamma(1-alpha)^2/Gamma(1-2 alpha)`) are correct.

Upper bound, three ranges.
- `r < eta k`: `<= T((1-eta) k) P(S_m < eta k) <= ((1-eta)^{-alpha} + delta_k) T(k)`, with `1-eta in [1/2, 1]` inside the range of `delta_k`. Correct.
- `eta k <= r <= (1-eta) k`: `<= T(eta k) P(S_m >= eta k) <= C m T(eta k)^2 <= C_eta (m T(k)) T(k) <= C_eta epsilon T(k)`. Correct; uses (R2) with `c = 1/eta`, so `k >= 1/eta`.
- `r > (1-eta) k`, `i = k - r in [1, eta k)`, dyadic blocks `[w/2, w)`, `w = 2^l`. Note the blocks reach `w < 2 eta k`, not `w <= eta k` as the text says; this only requires `eta < 1/4` where the text has `eta < 1/2`, and `eta -> 0` at the end, so it is harmless. A block contributes at most `T(w/2) P(S_m in [k-w, k))`.
  - Bound by `lem:cd`(ii): each of the `w` points `x in [k-w, k)` has `x >= k/2`, so `u_m(x) <= C (m/a_m) T(x) <= C (m/a_m) T(k)` by (R2). Correct.
  - Bound by the one-jump lemma. The display `P(S_m >= k-w) - P(S_m >= k) <= m T(k) [T(k-w)/T(k) - 1 + 2 varrho T(k-w)/T(k)]` follows from `|P(S_m >= y)/(m T(y)) - 1| <= varrho` at `y = k` and `y = k - w` and `T(k-w) >= T(k)`. At `y = k`: `m T(k) <= epsilon` and `k >= k/2`, in range. At `y = k - w`: `y >= k/2` holds, but `m T(k-w) <= epsilon` is not given; only `m T(k-w) <= (T(k-w)/T(k)) epsilon <= 2 epsilon` for large `k`. So the pair `(m, k-w)` lies in the index set of `varrho(2 epsilon, k)`, not necessarily of `varrho(epsilon, k)`. Repair: write `varrho(2 epsilon, k)` throughout. Since `limsup_k varrho(2 epsilon, k) -> 0` as `epsilon -> 0` by Lemma `lem:onejump`, the final limits are unchanged. This is the only genuine misstep in the three proofs.
  - `T(k-w)/T(k) - 1 <= (1 - w/k)^{-alpha} - 1 + delta_k <= C w/k + delta_k` for `w/k <= 1/2`. Correct. The text then writes `3 varrho`; from the stated bound `T(k-w)/T(k) <= 2` one gets `2 varrho . 2 = 4 varrho`. `3 varrho` is right if `eta` is small enough that `T(k-w)/T(k) <= 3/2`. Either way the constant is immaterial since `varrho -> 0`. One-token repair.
  - Blocks `w <= theta a_m`: `C (m T(k)/a_m) sum_{w <= theta a_m} w T(w/2) <= C (m T(k)/a_m) theta a_m T(theta a_m)` by (R4), and `theta T(theta a_m) <= C theta^{1 - alpha'} T(a_m)` by Potter's bound for `T` (upper bound with exponent `alpha' = alpha + delta`), then `m T(a_m) <= C`. For small `m`, where `theta a_m < x_0`, Potter does not apply directly; but then the sum is empty unless `theta a_m >= 2`, and for `2 <= theta a_m < x_0` one bounds `psi(theta a_m) <= C_0` with `psi(x) = x T(x)` and `psi(a_m) >= c (a_m/x_0)^{1-alpha'} psi(x_0) >= c (2/(theta x_0))^{1-alpha'}`, which gives the same `theta^{1-alpha'}` with a constant depending only on `T`. So the bound `C theta^{1-alpha'} T(k)` is uniform in `m >= 0`; the text's "by (R4) and Potter's bounds" covers this after that one-line remark. Correct.
  - Blocks `theta a_m < w <= eta k`: `m T(k) [ (C/k) sum_{w <= eta k} w T(w/2) + (delta_k + 3 varrho) sum_{w > theta a_m} T(w/2) ]`. First piece: `(C/k) eta k T(eta k) = C eta T(eta k) <= C eta^{1-alpha} T(k)` for large `k`, times `m T(k) <= epsilon`: `C epsilon eta^{1-alpha} T(k)`. The text's intermediate expression "`eta^{1-alpha} k T(eta k)/k`" should read `eta T(eta k)`; its final form `C eta^{1-alpha} epsilon T(k)` is right, and in the final display this term is absorbed into `C_eta epsilon`. Second piece: `sum_{w > theta a_m} T(w/2) <= C T(theta a_m)` by (R4) (for `theta a_m < 1` the sum is a finite constant and `T(theta a_m) = 1`), and `m T(theta a_m) <= C theta^{-alpha'}` by Potter for `theta a_m >= x_0` and by `m <= C/T(a_m) <= C/T(x_0/theta) <= C theta^{-alpha'}` otherwise. Hence `C theta^{-alpha'} (delta_k + 3 varrho) T(k)`. Correct, uniformly in `m`.

Final display and limits. `sup_{m T(k) <= epsilon} q_{m+1}(k)/T(k) <= (1-eta)^{-alpha} + delta_k + C theta^{1-alpha'} + C_eta epsilon + C theta^{-alpha'} (delta_k + 3 varrho(2 epsilon, k))`. The left side of the target statement, `limsup_k sup_{m T(k) <= K} |q/T - phi(m T(k))|`, does not depend on `epsilon, eta, theta`; on `[epsilon, K]` it is `0`, on `[0, epsilon]` it is at most the display's `limsup_k` plus `sup_{[0,epsilon]} |phi - 1| = O(epsilon)` minus the lower bound `1 - C epsilon`. The constants `C` (from `T` alone) and `C_eta` (from (R2) with `c = 1/eta`) do not depend on `epsilon` or `theta`, so letting `k -> inf`, then `epsilon -> 0` (which removes `varrho` by Lemma `lem:onejump` and `C_eta epsilon`), then `theta -> 0`, then `eta -> 0` gives `0`. The order is legitimate. Correct.

### Verdict

Proved as written, for (i), (ii) and the identification of the limit with `phi`. Three one-token repairs to the proof of (ii), none of which touches the statement or the limits:
1. `varrho(epsilon, k)` must be `varrho(2 epsilon, k)` (or `varrho(epsilon', k)` with any `epsilon' > epsilon` and `k` large), because the one-jump lemma is applied at `y = k - w` where only `m T(k-w) <= 2 epsilon` holds. This is the smallest missing implication, and it is supplied by the same lemma.
2. `3 varrho` is `4 varrho` under the stated `T(k-w)/T(k) <= 2`, or keep `3 varrho` and say `eta` is small.
3. The dyadic blocks reach `w < 2 eta k`; either cap each block at `eta k` or take `eta < 1/4`. The intermediate "`eta^{1-alpha} k T(eta k)/k`" should be `eta T(eta k)`.

---

## Cross-cutting checks

- Uniformity in `m` was the main adversarial target in all three lemmas, since each is stated for all `m >= 1` (or `m >= 0`). In `lem:onejump` no step depends on `m` beyond `m T(y) <= epsilon`. In `lem:fourier` the only `m`-dependent inputs are `inf_m m T(a_m) > 0` and `a_m <= C m^{1/alpha + delta}`, both valid for all `m >= 1`. In `lem:Q`(ii) the Potter steps on the blocks `w <= theta a_m` and `w > theta a_m` need a remark for bounded `m` (given above); the bound survives.
- Ranges of substitutions. `t = s/a_m` maps `[0, pi]` to `[0, pi a_m]`; the three ranges `s <= 1`, `1 <= s <= a_m/x_0`, `s >= a_m/x_0` cover it, with the last empty when `a_m < x_0`. Checked.
- Potter's bounds are used (a) as (R2) with a fixed ratio, which needs the argument above the ratio; (b) as the two-sided power bounds with exponent `alpha +- delta` above a threshold `x_0`, which needs `delta < alpha` in `lem:fourier`(ii), (iii) and `alpha' = alpha + delta < 1` in `lem:Q`(ii) (the text does take `alpha' in (alpha, 1)` there). Checked.
- Hypotheses. `lem:onejump` uses only (RV). `lem:fourier` uses (RV) and (SPAN) (the latter only for `|varphi| < 1` away from `0`, and through Gnedenko in the last claim of (ii) via `lem:sums`(iii), which is not needed there anyway). `lem:Q` uses (RV), (SPAN) (through `lem:cd`(i)) and `lem:cd`(ii). None uses (SRT) or (LB). Consistent with the statements.

## Provenance

- `check_lemQ3.py`: Zolotarev integral for the stable density, Mittag-Leffler series for `phi`, FFT convolutions for `u_m` truncated to `[0, k)`, exact tail `T(k) = zeta(1+alpha, k)/zeta(1+alpha)`.
- `check_lemQ3_output.txt`: the run quoted above.
