# Paper F, window O2: audit of Theorem O2

25 October 2026. Audited: `01_report.md` (Theorem O2, Lemmas 1-4, section 4),
against `paperF/sec_setting.tex`, `sec_bulk.tex` (Theorem A), `sec_bigjump.tex`
(Theorem B, `lem:no-giant`, `lem:one-giant`, `cor:bigjump-lower`, `rem:theta`) and
`sec_appendix.tex` (`lem:stable`). Only the mathematics was judged. Nothing in the
paper was edited.

## Verdict

**Correct after a stated restriction.** Theorem O2 (a), (b), (c) holds as stated. I
found no broken implication in Lemmas 1-4 or in section 4. The restriction is on
what the theorem is said to give F: it does **not** remove the window. It shrinks
the undescribed range from `K <= x <= K lambda_N` to `K <= x <= (1+delta) x*_N`,
and on that range it describes `P_N` only on the logarithmic scale. The proposed
edits "there is no window" (window paragraph after Theorem B, intro lines 108-115,
abstract) overclaim and should be replaced by that wording.

## 1. Claim card

- Objects: fresh start, `x = (k-pN)/B_N`, `G_N` from `eq:G`, `n_N = N/s`,
  `psi(l) = log E e^{-l(X_- - mu_-)}`,
  `Lambda_N(x) = sup_l [l (x/p) B_N - n_N psi(l)]`. `x*_N` is the root of
  `Lambda_N(x) = alpha_+ log(1/theta_{+,N})`.
- Hypotheses: those of Theorem B(b) ((RV), (SPAN) for both signs, (LR) plus),
  `b_{+,N} <= b_{-,N}` for large `N` (so `B_N = b_{-,N}`), `K <= x <= X_N` with
  `X_N B_N = o(N)`. Part (c) also needs `theta_{+,N} -> 0`.
- (a) `max{(1-eps)G_N, B_N^{-1}e^{-(1+eps)Lambda_N}} <= P_N <= (1+eps)G_N + B_N^{-1}e^{-(1-eps)Lambda_N}`.
- (b) `Lambda_N(x) -> c_Z (x/p)^beta` for fixed `x`, with `beta = alpha_-/(alpha_- - 1)`.
  Potter bounds `x^{beta +- delta}`, the scaling `Lambda_N(cx)/Lambda_N(x) -> c^beta`,
  and exact power form under `T_- ~ c_- n^{-alpha_-}`.
- (c) `P_N/G_N -> 1` uniformly from `(1+delta)x*_N B_N` to `N`. `P_N/G_N -> infinity`
  uniformly on `[K_0, (1-delta)x*_N]`. `x*_N = (log 1/theta_+)^{1/beta + o(1)} = o(lambda_N)`.
  Under a pure power minus tail, `x*_N ~ p (alpha_+ log(1/theta_+)/c_Z)^{(alpha_- - 1)/alpha_-}`.

## 2. Independent derivation of the crossover

I did this before reading section 1 of the report.

- Big jump. `B_N G_N ~ (alpha_+/mu_-) N T_+(L) B_N/L`. With `N T_+(L) ~ s T_+(L)/T_+(b_+)`
  and `L/b_+ = x/((1-p)theta_+)`, Potter gives
  `-log(B_N G_N) = alpha_+ log(1/theta_+) + O(log x) + o(log 1/theta_+)`. For pure
  powers, `B_N G_N ~ alpha_+ (1-p)^{alpha_+} theta_+^{alpha_+} x^{-alpha_+-1}`, which matches
  `rem:no-single-formula` with the factor `theta_+^{alpha_+}`.
- Light side. The plus sums stay within `O(b_+)` of their mean, so `m ~ k/mu_+ = n_N(1+o(1))`,
  and the minus deficit is `m mu_- - j = (k - pN)/p = (x/p) B_N`. The cost is
  `Lambda_N(x)`. With `n_N psi(u/B_N) -> K u^alpha` (`lem:stable`(i)), it tends to
  `sup_u(u y - K u^alpha) = (alpha-1) alpha^{-beta} K^{-1/(alpha-1)} y^beta` at
  `y = x/p`. This is the report's `c_Z`. It is the left-tail exponent of `Z_-` in
  the normalization of `eq:profile`.
- Balance. `c_Z (x/p)^beta = alpha_+ log(1/theta_+) (1+o(1))` gives the stated `x*_N`,
  with exponent `(alpha_- - 1)/alpha_-` and the stated constant. The terms `log x`
  and `O(1)` are of lower order because `x*_N` grows only like a power of
  `log(1/theta_+)`. A multiplicative `1 +- delta` in `x` moves `Lambda_N` by the
  factor `(1 +- delta)^beta`, so the `(1 +- delta)` form of (c) is the right
  resolution.

## 3. Line-by-line checks

**Lemma 1.**
- (ii) The expansion `phi_1 ~ K T(1/l)` is that of `lem:stable`(i) at real `xi`, and
  `l^2 = o(T(1/l))` holds since `alpha < 2`.
- (iii) The convexity sandwich `(c-1) l psi'(l) <= psi(cl) - psi(l)` is correct in
  both directions.
- (iv) It needs `E_l X^2 <= e^{l mu} E[X^2 e^{-lX}]`, which holds since `psi >= 0`.
  The Karamata step is correct for `l <= 1`.
- (v) Inversion of RV at `0+`, the envelope formula `(psi*)' = l_v` and
  `psi* = (alpha - 1 + o(1)) psi(l_v)` are correct.
- The facts on `Lambda_m(d)` follow: monotone in `m` and `d`; stable when `d/m -> 0`,
  `m'/m -> 1`, `d'/d -> 1`; and `Lambda_{cm}(d)/Lambda_m(d) -> c^{1-beta}`.

**Lemma 2 (tilted local bound).** The tilt is legitimate. `psi` is finite for all
`l >= 0` because `X >= 1`, so no moment condition beyond (RV) is needed.
- `||f_l - f||_1 -> 0` and (SPAN) handle `delta <= |t| <= pi`.
- On `n <= 1/l`, `f_l >= e^{-1-psi(l_0)} f`, and `1 - cos u >= 2u^2/pi^2` for `|u| <= pi`.
  The mass of `[R/2, R]` together with the mass of `[1, R/4]` gives
  `1 - |phi_l|^2 >= c t^2 R^2 T(R)`.
- With `R = pi/|t|` on `pi l <= |t| <= delta`, the substitution `t = s/a(m)` and
  Potter (which needs `a/s >= x_delta`, ensured by `delta = pi/R_0` with `R_0` large)
  give `C/a(m)`.
- The order of choices (`R_0`, then `delta`, then `l_0 <= 1/R_0`) is consistent.
- The prefactor `C(l + 1/a(m))` is crude but enough for a logarithmic statement.

**Lemma 3.**
- `E_l S_m = m mu - d` holds. The density bound `e^{-Lambda - 2 l sigma}` on the
  Chebyshev window is correct.
- `l sigma <= C (m T(1/l))^{1/2} <= C Lambda^{1/2}` holds while `l <= l_0`.
- `sigma <= C a(m)` holds when `l a(m) >= 1`, by Potter with `alpha + delta' < 2`.

**Lemma 4.**
- `d >= D a(m)` forces `l' a(m-n) >= 1`. From Lemma 1(v),
  `l ~ (d/(alpha K a))^{1/(alpha-1)}/a` on this scale.
- So `2 sigma' <= R_delta a(n)`. Gnedenko's theorem and `g_- > 0` on `R` give the
  factor `c_delta/a(m)`.
- The cost `Lambda_{(1-delta)m}(d) ~ (1-delta)^{1-beta} Lambda_m(d)` has the right
  direction: it is a loss factor greater than one.

**(a), lower bound.** Max of two separate lower bounds, which is legitimate.
- `cor:bigjump-lower` needs only `k >= pN + K B_N`, which is `x >= K`.
- In the light term, `q^+_{m+1}(k) >= u^+_m(k-1) T_+(1)` follows from `eq:q-cover`. On
  `W`, `a_+(m)/b_{+,N} -> 1` and `b_{+,N} -> infinity`, so Gnedenko for the plus runs
  gives `c/b_+`, and `#W ~ 2b_+/mu_+` cancels it.
- On `W`, `d_2 = (x/p)B_N + O(b_+)`. When `theta_+` does not tend to 0 the relative
  error is `O(1/x)`, which is absorbed by taking `K` large. The minus start shifts
  `W` by one, which is correct.

**(a), upper bound.** A sum, which is legitimate.
- Dropping the subtracted term of `eq:giant-split` is valid.
- `lem:one-giant` holds for every fixed `eta <= 1/2` once `L >= K B_N`, with `K`
  depending on `eta = eps/32`. That is allowed. It also absorbs the mixed
  configurations (a giant run plus a minus shortfall) through `lem:spread`.
- Set A. The half-split and `lem:truncated` with `w = eta L` and `z = eps L/4` give the
  exponent `eps/(8 eta) = 4`. For `m <= 1` the term vanishes since `eps/2 > eta`.
  Divided by `G_N >= c_8 (N/L) T_+(L)` (valid because `j ~ (1-p)N >= J_0`), the
  contribution tends to 0.
- Set B. `d_1 < eps L` gives `d_2 > (1-eps)(x/p)B_N`. Bounding by the supremum of the
  minus factor times kernel sums at most 1 is the `lem:no-giant` scheme. The single
  tilt `l*` works because `m' <= m''`, `d' >= d''` and `psi >= 0`. The scaling gives
  `(1+eps)^{1-beta}(1-eps)^beta >= 1 - C eps`. The range `m > (1+eps) n_N` has
  `d_2 >= eps mu_- m/2` in both subcases (`m` below or above `2N/s`), and a fixed
  `l_1` gives `e^{-cN} = o(G_N)`. The report's claim `m > n_N` is true but not needed.
- The factor `x^C` is absorbed since `Lambda_N(x) >= c x^{beta - delta}` and `x >= K`.

**(b).**
- The conjugate of the pointwise limit `K u^alpha` gives the fixed-`x` limit.
- The uniform statements use only `x v_N <= X_N v_N -> 0`, with
  `v_N = B_N/(p n_N)`, and the uniform convergence theorem and Potter for
  `psi* in RV_beta(0+)`.
- The pure-power constant checks: `A* c_-^{1/(alpha-1)} = c_Z`, using
  `B_N^beta n_N^{1-beta} -> c_-^{1/(alpha-1)}`.

**(c).**
- `-log(B_N G_N) = alpha_+ log(1/theta_+)(1+o(1))` needs `log x = o(log 1/theta_+)`.
  This holds on `x <= K lambda_N`, which is the only range where it is used.
- (c1): (a) on `[(1+delta)x*_N, K_1(eps) lambda_N]`, then Theorem B(b) beyond. One
  must take `X_N = K_1(eps) lambda_N`, which (a) allows since `lambda_N B_N = o(N)`
  by `lem:rv`(v). This should be stated explicitly. The step needs
  `(1-eps)(1+delta)^beta > 1`.
- (c2): needs `(1+eps)(1-delta)^beta < 1`. On `[K_0, K(eps)]` it uses Theorem A(c)
  with `lem:profile`(d), and the bound in `rem:theta` for `B_N G_N -> 0`. Correct.
- `x*_N -> infinity` and `x*_N = (log 1/theta_+)^{1/beta + o(1)}` hold, and
  `x*_N = o(lambda_N)` since `1/beta < 1/2`.

## 4. Does it settle `rem:theta`?

The remark leaves open whether the factor in front of `B_N` must be as large as
`lambda_N`. O2(c) answers it to first order. The threshold is `x*_N`, which is
`o(lambda_N)`: the zone starts at `(1+delta)x*_N B_N` and cannot start at
`(1-delta)x*_N B_N`. That part is settled.

O2 does not give the following:
- an asymptotic for `P_N` with relative error `o(1)` on `[K, (1+delta)x*_N]`. Below
  `x*_N`, `P_N` is known only up to factors `e^{+-eps Lambda_N}`, which are
  unbounded;
- the behaviour inside the strip `(1 +- delta)x*_N`;
- any rate.

The report's own section 0 says this. Its "Consequences for F" bullet does not, and
that bullet is the overclaim noted in the verdict. Two smaller cautions:
- The constant formula needs the pure-power minus tail. Under (RV) alone only the
  exponent `1/beta + o(1)` holds, as the report states.
- `x*_N` is defined with `alpha_+ log(1/theta_+)`, not with `-log(B_N G_N)`. The two
  agree to first order, which is all (c) uses.

## 5. Numeric spot-check

I wrote my own script in a scratch folder, run with `py -I`. It computes the exact
law by a different route from the report: the fresh-plus identity
(`prop:fresh-identity`), with `u^+-_m` and `q^+-_m` built by FFT convolution
(mass error below `1e-12`). It also computes its own `G_N`, its own Cramer transform
`Lambda~`, `x_c` (first `x` with `P <= 2G`) and `x*` (`Lambda~ = -log(B_N G_N)`).
The setting is `N = 3000`, `alpha = 1.8`.

| w | x_c | x* | x_c/x* | P/G at x ~ 4 |
|---|---|---|---|---|
| 0.1 | 3.793 | 2.794 | 1.358 | 1.806 |
| 0.01 | 3.643 | 3.134 | 1.162 | 1.697 |
| 0.001 | 3.708 | 3.446 | 1.076 | 1.681 |

These agree with `out_crossover_N3000_a1.8.txt` to every printed digit, and the
ratio does move toward 1.

The trend is weak evidence for (c), for three reasons:
- It tests the finite-`N` balance with `Lambda~` and `-log(B_N G_N)`, not the
  theorem's `x*_N`.
- `Lambda~` is far from its limit at this `N` (about 16 against
  `c_Z(x/p)^beta ~ 4` at `x = 4`), and it is steep near the hard wall
  `X_- >= 1`. Any balance-type definition clusters there.
- For `w <= 0.001`, `b_{+,N} = 1`, so `theta_+` is nominal, and the shrinking
  of `G_N` comes from the tail constant, not from `theta_+`.

The report says the asymptotic scale cannot be seen at computable `N`, and I agree.
