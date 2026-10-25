# Paper F, open window (O2): report

25 October 2026. Paper F is `kagey-problems/problem131/paperF` (problem131_levy.tex
and its sections, read as they stand in the working tree). Nothing in the paper was
edited. All scripts are in this folder and run with `py -I`.

## 0. Status in one paragraph

**Proved (below, complete modulo standard regular-variation facts cited to BGT):**
a two-sided estimate on the logarithmic scale across the whole window. It shows that
when the plus scale is the smaller one there is no window. The big-jump asymptotics
`P_N ~ G_N` hold from `(1+delta) x*_N B_N` on, and fail by an unbounded factor up to
`(1-delta) x*_N B_N`. Here `x*_N` is defined by an exact Cramer transform of the
minus runs. It has order `(log 1/theta_{+,N})^{(alpha_- - 1)/alpha_- + o(1)}`, and
under a pure power tail for the minus runs it equals
`x*_N ~ p (alpha_+ log(1/theta_{+,N}) / c_Z)^{(alpha_- - 1)/alpha_-}` with an explicit
`c_Z`. This answers the question left open in Remark `rem:theta` ("We do not show that
the factor must be as large as `lambda_N`"). The factor need not be that large: the
right one is `x*_N`, which is `o(lambda_N)`.

**Not proved:** a uniform asymptotic with relative error `o(1)` through the
crossover, for instance by the composite `h_N/B_N + G_N - tau_N/B_N`. That needs an
exact (relative-error) local Cramer estimate on the light side together with a
second-order tail condition. Section 6 states it as a precise conjecture, and
section 5 names the first missing implication.

**Numerics:** the plan's table is reproduced independently, and the predictions were
filed first (`00_predictions.md`). The main new finding is that in the plan's
example the composite's flatness for `x >= 4` does **not** come from the
light/big-jump crossover. There the light term is below `e^{-17}/B_N`, while
`B_N P_N ~ e^{-6}`. What `P_N - G_N` measures there is the finite-size correction to
the kernel. In that example the crossover actually sits near `x ~ 2.5-3`.

## 1. Check of the plan's crossover formula

Derived by hand before any run. On the plus side at `x = (k-pN)/B_N`, with
`B_N = b_{-,N}`, there are two competing mechanisms:

- **One plus run of length about `L_k`.** Here `B_N G_N(k) ~ tau_N(x) =
  alpha_+((1-p)theta_+)^{alpha_+} x^{-alpha_+-1}`. So
  `-log(B_N G_N) = alpha_+ log(1/theta_+)(1+o(1))` uniformly for `1 <= x <= K lambda_N`,
  by Potter's bounds, since `log x = O(log log 1/theta_+)`.
- **No giant plus run.** Then the `~N/s` minus runs fall short of their mean by
  `(x/p)B_N`. This costs `exp(-Lambda_N(x))`, where
  `Lambda_N(x) = sup_{l>=0}[ l (x/p) B_N - (N/s) psi_-(l) ]` and
  `psi_-(l) = log E e^{-l(X_- - mu_-)}`. For fixed `x` this tends to
  `c_Z (x/p)^beta`, with `beta = alpha_-/(alpha_- - 1)` and
  `c_Z = (alpha_- - 1) alpha_-^{-beta} K_-^{-1/(alpha_- - 1)}` (here `K = -Gamma(1-alpha)`).
  This is the light-tail exponent of `Z_-` in the normalization of `eq:profile`.

The order `(log 1/theta_+)^{(alpha_- - 1)/alpha_-}` in the plan is **correct**. The
constant above is new. Under (RV) alone, `Lambda_N(x)/x^beta` may drift by a slowly
varying factor as `x -> infinity` (Potter gives `x^{beta +- delta}`). So in general
only `x*_N = (log 1/theta_+)^{(alpha_- - 1)/alpha_- + o(1)}` holds. The asymptotic
equivalence (`~`) holds when `T_-(n) ~ c_- n^{-alpha_-}`.

## 2. The theorem

Hypotheses: those of Theorem `thm:bigjump`(b), meaning (RV) and (SPAN) for both signs
and (LR) for the plus sign, with a fresh start of either sign. In addition assume
`b_{+,N} <= b_{-,N}` for all large `N`, so that `B_N = b_{-,N}`. Write
`x = x_{N,k}`, `n_N = N/s`, and let `Lambda_N` be as in section 1. Take `G_N` as in
`eq:G`, `lambda_N` as in `eq:lambdaN`, and `x*_N` as the unique root of
`Lambda_N(x) = alpha_+ log(1/theta_{+,N})`.

**Theorem O2.**

(a) *Two-sided estimate.* For every `eps > 0` there is `K`, and for every `X_N` with
`X_N B_N = o(N)` there is `N_0`, such that for `N >= N_0` and `K <= x <= X_N`:

    max{ (1-eps) G_N(k), B_N^{-1} e^{-(1+eps) Lambda_N(x)} }
        <= P_N(k) <= (1+eps) G_N(k) + B_N^{-1} e^{-(1-eps) Lambda_N(x)} .

(b) *The exponent.*
- For fixed `x`, `Lambda_N(x) -> c_Z (x/p)^beta`.
- For every `delta > 0`, `c x^{beta-delta} <= Lambda_N(x) <= C x^{beta+delta}` on
  `1 <= x <= X_N`.
- `Lambda_N(cx)/Lambda_N(x) -> c^beta` uniformly on `1 <= x <= X_N`, for fixed `c > 0`.
- If `T_-(n) ~ c_- n^{-alpha_-}`, then `Lambda_N(x) = c_Z (x/p)^beta (1+o(1))`
  uniformly on `1 <= x <= X_N`.

(c) *Sharp crossover.* Assume in addition `theta_{+,N} -> 0`.
- `x*_N -> infinity`, `x*_N / lambda_N -> 0` and
  `x*_N = (log 1/theta_{+,N})^{(alpha_- - 1)/alpha_- + o(1)}`.
- For every `delta in (0,1)` and every fixed `K_0 > 0`:

      (c1)  sup_{pN + (1+delta) x*_N B_N <= k <= N} |P_N(k)/G_N(k) - 1| -> 0 ,
      (c2)  inf_{pN + K_0 B_N <= k <= pN + (1-delta) x*_N B_N} P_N(k)/G_N(k) -> infinity .

- If `T_-(n) ~ c_- n^{-alpha_-}`, then
  `x*_N ~ p (alpha_+ log(1/theta_{+,N}) / c_Z)^{(alpha_- - 1)/alpha_-}`.

The same statements hold at the minus end with the signs exchanged.

Consequences for F:
- Remark `rem:theta` can be completed: the zone of Theorem `thm:bigjump`(b) starts at
  `(1+delta)x*_N B_N` and cannot start at `(1-delta)x*_N B_N`.
- The "window" paragraph after Theorem `thm:bigjump`, the intro (lines 108-115) and
  the abstract sentence "one window is described only in part" become "there is no
  window".

## 3. Lemmas on the minus runs

Throughout this section `X = X_-`, with `alpha = alpha_-`, `mu = mu_-`, `a = a_-`
and `T = T_-`. (RV) and (SPAN) are assumed for this sign.

**Lemma 1 (Laplace exponent).** Let `psi(l) = log E e^{-l(X-mu)}` for `l >= 0`.
- (i) `psi` is finite, smooth and strictly convex on `(0,inf)`, with
  `psi(0) = psi'(0+) = 0` and `psi >= 0` (Jensen). Moreover
  `psi'(l) = mu - E_l X` increases from `0` to `mu - x_min`, where `x_min = min supp X`
  and `E_l` is the mean under the tilted law `f_l(n) = f(n)e^{-l(n-mu)-psi(l)}`.
- (ii) `psi(l) ~ K T(1/l)` as `l -> 0`.
- (iii) `l psi'(l) ~ alpha psi(l)`.
- (iv) For `0 < l <= 1`, `Var_l X <= E_l X^2 <= C l^{-2} T(1/l)`.
- (v) `psi*(v) = sup_{l>=0}(lv - psi(l))` is attained at `l_v = (psi')^{-1}(v)` for
  `0 <= v < mu - x_min`. Moreover `l_v` is in `RV_{1/(alpha-1)}(0+)`, `psi*` is in
  `RV_beta(0+)`, and `psi*(v) = (alpha-1+o(1)) psi(l_v)`.

*Proof.*
- (ii) As in the proof of `lem:stable`(i),
  `phi_1(l) = E[e^{-lX} - 1 + lX] = int_0^inf (1-e^{-v}) Tbar(v/l) dv ~ K T(1/l)`, by
  dominated convergence with Potter's bound. Then
  `psi = lmu + log(1 - lmu + phi_1) = phi_1 + O(l^2)`, and `l^2 = o(T(1/l))` since
  `alpha < 2`.
- (iii) Since `psi'` is monotone, for `c > 1`:
  `(c-1) l psi'(l) <= psi(cl) - psi(l)`. Dividing by `psi(l)` and letting `l -> 0`,
  then `c -> 1`, gives the upper bound `alpha`. The case `c < 1` gives the lower bound.
- (iv)
  `E[X^2 e^{-lX}] <= sum_{n<=1/l} n^2 f(n) + sup_u(u^2 e^{-u}) l^{-2} T(1/l)`.
  The first sum is at most `2 sum_{n<=1/l} n T(n) <= 2 C_K l^{-2} T(1/l)` by
  `eq:karamata`. Also `E e^{-lX} >= e^{-mu}`.
- (v) `psi'` is in `RV_{alpha-1}(0+)` by (ii) and (iii), so its inverse is in
  `RV_{1/(alpha-1)}` (BGT Thm 1.5.12, transported to `0+`). The envelope theorem gives
  `(psi*)' = l_v`, so `psi*(v) = int_0^v l_u du` is in `RV_beta` (Karamata, BGT
  Prop. 1.5.8). Finally `psi*(v) = l_v psi'(l_v) - psi(l_v) = (alpha-1+o(1)) psi(l_v)`
  by (iii). ∎

Put `Lambda_m(d) = sup_{l>=0}(l d - m psi(l)) = m psi*(d/m)`. Since `psi >= 0`,
`Lambda_m(d)` is nonincreasing in `m` and nondecreasing in `d >= 0`. By (v) and the
uniform convergence theorem: if `d/m -> 0`, `m'/m -> 1` and `d'/d -> 1`, then
`Lambda_{m'}(d')/Lambda_m(d) -> 1`, and `Lambda_{cm}(d)/Lambda_m(d) -> c^{1-beta}`.

**Lemma 2 (local upper bound with tilting).** There are `l_0 in (0,1]` and `C` such
that for all `m >= 1`, all `l in [0, l_0]` and all integers `y`,

    P(S_m = y) <= C (l + 1/a(m)) exp( l (y - m mu) + m psi(l) ).

*Proof.* Change measure:
`P(S_m=y) = e^{l(y-m mu)+m psi(l)} P_l(S_m=y)` and
`P_l(S_m=y) <= (2pi)^{-1} int_{-pi}^{pi} |phi_l(t)|^m dt`, where `phi_l` is the
characteristic function of `f_l`.

1. *Away from zero.* `||f_l - f||_1 -> 0` as `l -> 0`. (SPAN) gives
   `|phi_0| <= 1 - 2c_delta` on `delta <= |t| <= pi`. So for small `l_0`,
   `|phi_l| <= 1 - c_delta` there, and the contribution is at most
   `2pi(1-c_delta)^m <= C/a(m)`.
2. *Near zero, lower bound on `1 - |phi_l|^2`.* For `n <= 1/l`,
   `f_l(n) >= e^{-1-psi(l_0)} f(n)`. With `1 - cos u >= 2u^2/pi^2` for `|u| <= pi` and
   `R = min(1/l, pi/|t|)`,

       1 - |phi_l(t)|^2 = E_l[1 - cos t(X-X')] >= c t^2 sum_{n,n'<=R} f(n)f(n')(n-n')^2 >= c t^2 R^2 T(R),

   for `R >= R_0`, using the mass `T(R/2) - T(R) >= cT(R)` in `[R/2, R]`. Take
   `delta = pi/R_0` and `l_0 <= 1/R_0`.
3. *Near zero, the two ranges.*
   - For `pi l <= |t| <= delta` this gives `1 - |phi_l|^2 >= c T(1/|t|)`. Then
     `|phi_l|^m <= exp(-c m T(1/|t|)/2)`, and the substitution `t = s/a(m)` with Potter
     gives an integral `<= C/a(m)`.
   - For `|t| <= pi l` the integrand is at most `1`, so this range contributes at most
     `2 pi l`. ∎

**Lemma 3 (window lower bound).** Let `0 < d < m(mu - x_min)`, `l = l_{d/m}` and
`sigma^2 = m Var_l X`. Then

    P(|S_m - (m mu - d)| <= 2 sigma) >= (3/4) e^{-Lambda_m(d) - 2 l sigma} .

If `l <= l_0`, then `l sigma <= C (Lambda_m(d))^{1/2}`. If also `l a(m) >= 1`, then
`sigma <= C a(m)`.

*Proof.*
- Under `P_l` the mean of `S_m` is `m mu - d`, since `psi'(l) = d/m`. Chebyshev gives
  `P_l(|S_m - (m mu - d)| <= 2 sigma) >= 3/4`. On that event the density
  `e^{l(S_m - m mu) + m psi(l)}` is at least `e^{-Lambda_m(d) - 2 l sigma}`.
- By Lemma 1(iv), `l sigma <= C (m T(1/l))^{1/2}`. By (ii) and (v),
  `m T(1/l) <= C m psi(l) <= C' Lambda_m(d)`.
- Also `sigma^2 <= C a(m)^2 (l a(m))^{-2} m T(a(m)/(l a(m))) <= C a(m)^2 (l a(m))^{alpha+delta'-2}`
  by Potter, with `delta' < 2 - alpha`. ∎

**Lemma 4 (point lower bound).** For every `delta in (0,1/2)` there are `D`, `c_delta`
and `epsilon_0` with the following property. Let `m >= m_0(delta)`, let `j` be an
integer, and put `d = m mu - j` with `D a(m) <= d <= epsilon_0 m`. Then

    P(S_m = j) >= c_delta a(m)^{-1} exp( -Lambda_{m-n}(d) - C Lambda_{m-n}(d)^{1/2} ),  n = floor(delta m).

*Proof.*
- Split `S_m = S' + S''`, with `m-n` and `n` summands. Let `I` be the window of
  Lemma 3 for `S'` with deficit `d`. Then
  `P(S_m=j) >= P(S' in I) inf_{|z - n mu| <= 2 sigma'} P(S_n = z)`.
- `d >= D a(m)` makes `l' a(m-n) >= 1` (since `l_{a(m)/m} a(m)` has a positive limit,
  by Lemma 1(v)). So `2 sigma' <= C a(m) <= R_delta a(n)`.
- Gnedenko's theorem (`lem:stable`(ii)) and `g_- > 0` on `R` give
  `P(S_n = z) >= c'_delta / a(n) >= c'_delta / a(m)`. ∎

## 4. Proof of Theorem O2

**Notation.** `L = L_k = xB_N s/mu_-` (from `eq:Lk`), `j = N-k`, and the deficits of
`lem:no-giant`: `d_1(m) = k - m mu_+` and `d_2(m) = m mu_- - j`, with
`mu_- d_1 + mu_+ d_2 = mu_- L`. Note `(mu_-/mu_+) L = (x/p) B_N` and
`a_-(n_N) = b_{-,N} = B_N`.

**(b).**
- For fixed `x`: `n_N psi(u/B_N) -> K u^alpha` by Lemma 1(ii) and `n_N T(B_N) = 1`.
  Convex conjugates of pointwise-convergent convex functions converge, and
  `sup_u(u x/p - K u^alpha) = c_Z (x/p)^beta`.
- The Potter-type bounds and the scaling come from
  `Lambda_N(x) = n_N psi*(x v_N)` with `v_N = B_N/(p n_N) -> 0` and `x v_N <= X_N v_N -> 0`,
  using Lemma 1(v) and the uniform convergence theorem.
- Under a pure power tail: `psi(l) ~ c_- K l^alpha`, hence
  `psi*(v) ~ A* v^beta` with `A* = (alpha-1) alpha^{-beta} (c_- K)^{-1/(alpha-1)}`, and
  `a(t) ~ (c_- t)^{1/alpha}`. Substituting gives `c_Z (x/p)^beta` uniformly while
  `x v_N -> 0`.

**(a), lower bound.**
- `P_N(k) >= (1-eps) G_N(k)` for `x >= K` is Corollary `cor:bigjump-lower`.
- Light term, plus start. Keep in `prop:fresh-identity` the terms
  `u^-_m(j) q^+_{m+1}(k)` with `m in W = {m : |k - 1 - m mu_+| <= b_{+,N}}`.
- By `eq:q-cover`, `q^+_{m+1}(k) >= u^+_m(k-1) T_+(1)`. By `lem:stable`(ii) for the
  plus runs (here `a_+(m)/b_{+,N} -> 1` on `W`, and `b_{+,N} -> infinity`), this is
  `>= c/b_{+,N}`. Since `#W >= b_{+,N}/mu_+`,
  `P_N(k) >= c min_{m in W} u^-_m(j)`.
- On `W`: `d_2(m) = (x/p)B_N + O(b_{+,N})` and `m/n_N = 1 + O(xB_N/N) -> 1`.
- Lemma 4 applies when `x >= 2pD`. With the scaling after Lemma 1 it gives
  `u^-_m(j) >= c_delta B_N^{-1} exp(-(1-delta)^{1-beta}(1+o(1)) Lambda_N(x) - C Lambda_N(x)^{1/2})`.
- Since `Lambda_N(x) >= c K^{beta-delta'}` for `x >= K`, taking `delta` small and `K`
  large gives `>= B_N^{-1} e^{-(1+eps) Lambda_N(x)}`.
- For a minus start, use the terms `u^-_m(j) q^+_m(k)`, with `W` shifted by one.

**(a), upper bound.**
- Take `g = ceil(eta L)` with `eta = eps/32` in `eq:giant-split`. Drop the subtracted
  term and use `lem:one-giant` (valid for `L >= KB_N`):
  `P_N(k) <= P(A_N=k, M_N < eta L) + (1+eps) G_N(k)`.
- To bound the first term, redo `lem:no-giant` with `L/2` replaced by `eps L`. Let
  `A = {m : d_1(m) >= eps L}` and `B` its complement.
- *Indices in `A`.* The argument of `lem:no-giant` applies word for word: a half-split,
  `lem:truncated` with `w = eta L` and `z = eps L/4`, so the exponent is
  `eps/(8 eta) = 4`. It gives `C (N T_+(L))^4 / b_{+,N}`. Divided by
  `G_N >= c (N/L) T_+(L)` (see the proof of (b) in F), this is
  `<= C (NT_+(L))^3 L/b_{+,N} -> 0`, by `eq:NT-bounds` with `L/b_{+,N} >= K`.
- *Indices in `B`.* Here `d_2(m) > (1-eps)(x/p)B_N` and `m > n_N`.
  - Every minus factor in `E_1` and `E_2` (either start) is at most
    `mu_- sup{u^-_{m'}(j') : m' in {m-1, m}, m' mu_- - j' >= d_2(m) - mu_-}`. Each
    kernel sum of `eq:kernel-sums` is at most 1.
  - For `n_N < m <= (1+eps) n_N`: apply Lemma 2 with the single
    `l* = l_{v''}`, where `v'' = d''/m''`, `m'' = (1+eps) n_N` and
    `d'' = (1-eps)(x/p)B_N - 2 mu_-`. Since `psi >= 0`, every such `(m', d')` has
    `l* d' - m' psi(l*) >= Lambda_{m''}(d'')`. Also `l* <= C x^C / B_N` by
    Lemma 1(v) and Potter, and `a_-(m') >= B_N/2`. The scaling gives
    `Lambda_{m''}(d'') >= (1 - C eps) Lambda_N(x)`.
  - For `m > (1+eps) n_N`: we have `d_2 >= mu_- eps m/2`. Use a fixed `l_1` with
    `psi(l_1) <= l_1 mu_- eps/4`. This gives `<= C e^{-cN}`.
- Altogether,
  `P(A_N=k, M_N < eta L) <= eps G_N + C x^C B_N^{-1} e^{-(1-C eps)Lambda_N(x)} + C e^{-cN}`.
  Since `log x = o(Lambda_N(x))` on `x >= K`, and `e^{-cN} = o(G_N)`, the upper bound
  follows. ∎

**(c).**
- `Lambda_N` is continuous and increasing, with `Lambda_N(0) = 0`. By (b),
  `Lambda_N(x) <= C x^{beta+delta}` on bounded sets, so `x*_N -> infinity`. Also
  `Lambda_N(lambda_N) >= c lambda_N^{beta-delta} >> log(1/theta_+)`, since `beta > 2`.
  So `x*_N <= lambda_N`, and indeed `x*_N = (log 1/theta_+)^{1/beta + o(1)} = o(lambda_N)`.
- Uniformly for `1 <= x <= K lambda_N` (note `K lambda_N B_N = o(N)` by `lem:rv`(v)),
  section 1 gives `log(B_N G_N) = -alpha_+ log(1/theta_+)(1+o(1))`. The proof uses
  `G_N >= c(N/L)T_+(L)`, the upper bound `eq:G-size`, and Potter for `T_+` at ratio
  `y = x/((1-p)theta_+)`.
- (c1), on `(1+delta)x*_N <= x <= K lambda_N`.
  - By the scaling in (b),
    `Lambda_N(x) >= (1+delta)^beta (1-o(1)) alpha_+ log(1/theta_+)`, and
    `Lambda_N(x) >= c x^{beta-delta}`.
  - So the light term of (a) divided by `G_N` is at most
    `exp(-[(1-eps)(1+delta)^beta - 1 - o(1)] alpha_+ log(1/theta_+) + C log x) -> 0`.
  - Hence `1 - eps <= P_N/G_N <= 1 + 2 eps`.
  - For `x >= K lambda_N`, Theorem `thm:bigjump`(b) applies directly.
- (c2), on `K <= x <= (1-delta)x*_N`.
  - The lower bound of (a) and
    `Lambda_N(x) <= (1-delta)^beta (1+o(1)) alpha_+ log(1/theta_+)` give
    `B_N P_N >= theta_+^{(1+eps)(1-delta)^beta(1+o(1)) alpha_+}`, while
    `B_N G_N <= theta_+^{alpha_+ - o(1)}`. The ratio tends to infinity.
  - On `K_0 <= x <= K`: by `thm:bulk`(c) and `lem:profile`(d), `B_N P_N >= c`, and
    `B_N G_N -> 0` by the bound in `rem:theta`.
- The pure-power formula follows from the last item of (b). ∎

**F labels used:**
- section 2 of F: `prop:fresh-identity`, `eq:q-cover`, `eq:kernel-sums`, `eq:G`,
  `eq:Lk`, `eq:lambdaN`, `eq:karamata`, `eq:NT-bounds`, `lem:rv`(i),(ii),(v),
  `lem:profile`(d);
- the appendix lemma `lem:stable`(i),(ii);
- section 3 of F: `thm:bulk`(c);
- section 4 of F: `lem:giant`/`eq:giant-split`, `lem:truncated`, `lem:no-giant` (its
  set-A argument and the minus-start bookkeeping), `lem:one-giant`, `eq:G-size`, the
  bound `G_N >= c_8 (N/L) T_+(L)` from the proof of `thm:bigjump`(b),
  `cor:bigjump-lower`, `thm:bigjump`(b), `rem:theta`.

**What I did not need:** a uniform rate in the tail of `h_N`. The F author pass
correctly says that F does not prove one. Theorem O2 never compares with `h_N` in the
window. Such a rate would be needed only for the composite (section 6). Its light
part follows from the classical light-tail expansion of `g_-` (Zolotarev 1986,
Thm 2.5.2, to be checked against the exact statement before use). Its heavy part
needs a separate convolution estimate, which I did not do.

**Audit flags for the proof** (points a referee would check):
1. Lemma 2 step 2 needs `l_0 <= 1/R_0`, with `R_0` chosen before `delta`. This order
   is consistent.
2. In the upper bound the single `l*` uses `m' <= m''`. The indices `m = m'' + O(1)`
   go to the `e^{-cN}` branch with a slightly smaller `eps`. This is harmless.
3. The B-index claim `m > n_N` follows from `d_1 < eps L`, which gives
   `m > n_N + (1-eps') x B_N/mu_+`.
4. In (a) the hypothesis `b_{+,N} <= b_{-,N}` is used, through `a_-(m') >= B_N/2`,
   to keep the prefactor `1/B_N`. Without it the prefactor is `1/b_{-,N}`. That case is
   not the window case, and I did not treat it.

## 5. First missing implication for the strong (composite) form

For the composite statement of section 6 to follow from the present proof, one needs
a local light-side estimate with **relative** error:

    u^-_m(m mu_- - d) = (1+o(1)) a_-(m)^{-1} g_-(-d/a_-(m))    uniformly for d <= C (log N)^{1/beta} a_-(m).

Under (RV) alone this is false at `d ~ x*_N a_-(m)`. There the exact exponent
`Lambda_m(d)` differs from `c_Z (d/a)^beta` by `(d/a)^beta * o(1)`, and
`(d/a)^beta` is about `log N`. So a second-order condition is needed, for instance
`T_-(n) = c_- n^{-alpha_-}(1 + O(n^{-rho}))`. With it, the error becomes
`O((log N) N^{-rho'}) -> 0`. Two further ingredients are needed:

- a tilted local CLT with the exact Gaussian prefactor, of Borovkov–Borovkov type for
  the left tail of a one-sided stable domain (statement not yet checked against the
  2008 book);
- a proof that the no-giant term splits as light term plus moderate-plus-jump cross
  terms, each matched by `h_N - tau_N`.

The first of these is the first missing implication.

## 6. Conjecture (fallback, precise)

**Conjecture O2-strong.** Assume:
- the hypotheses of Theorem O2(c);
- `T_-(n) = c_- n^{-alpha_-}(1 + O(n^{-rho}))` for some `rho > 0`;
- `T_+(n) = c_+ n^{-alpha_+}(1 + O(n^{-rho}))` for some `rho > 0`.

Let `C_N(k) = B_N^{-1} h_N(x) + G_N(k) - B_N^{-1} tau_N(x) 1_{x>=1}`. Then

    lim_{K->inf} limsup_{N->inf} sup_{pN + K B_N <= k <= pN + N/K} |P_N(k)/C_N(k) - 1| = 0.

The upper cut `N/K` keeps the comparison away from the ballistic range, where
`tau_N` is not the overlap of `h_N` and `G_N` (see section 7.2). In particular, near
`x*_N`:

    P_N(k) ~ B_N^{-1} p^{-1} g_-(-x/p) + G_N(k).

Weaker statements already proved: Theorem O2(a) is the logarithmic form of this, and
(c) gives the sharp location of the crossover.

## 7. Numerics

All runs are in this folder: `py -I <script>`. The library is `o2_lib.py`, all
scripts are LF with a header, and outputs are in `out_*.txt`.

### 7.1 Exactness of my recursion (P1: passed)

`py -I o2_checks.py` writes `out_checks.txt`. The recursion runs on (minus count,
plus count) through `prop:final-run`.
- Against brute-force enumeration for `N <= 12`, three law pairs: max abs diff
  `9.4e-16`.
- Against an independent forward Markov recursion on (count, sign, age) at `N = 300`:
  max relative diff `<= 2.6e-14`.
- Mass: `1 - sum P = 3e-14` at `N = 2000` and `7.5e-14` at `N = 5000`.

### 7.2 The plan's table (P2: passed)

`py -I o2_window_table.py 2000 5000` writes `out_window_table.txt`. Laws: zeta with
`alpha_+ = 1.9` and `alpha_- = 1.3`, plus start. Ratios are `P_N` over each
approximant.

| x | P/bulk 5000 (2000) | P/G | P/(bulk+G) | P/comp |
|---|---|---|---|---|
| 3 | 0.751 (0.655) | 15.9 (13.3) | 0.717 (0.624) | 0.751 (0.654) |
| 4 | 0.765 (0.576) | 3.71 (3.75) | 0.635 (0.499) | 0.766 (0.577) |
| 6 | 0.891 (0.811) | 1.75 (1.73) | 0.591 (0.553) | 0.915 (0.838) |
| 10 | 0.808 (0.741) | 1.24 (1.21) | 0.489 (0.459) | 0.905 (0.854) |
| 15 | 0.697 (0.616) | 1.09 (1.05) | 0.425 (0.388) | 0.889 (0.840) |
| 20 | 0.595 | 1.025 | 0.377 | 0.878 |

This agrees with the plan to two digits: the sum is about twice too large, and the
composite is flat and improving with `N`.

One discrepancy: at `x = 1` I get `P/comp = 1.114` (2000) and `1.042` (5000). The
plan reports 0.96 / 0.94, which equals its sum column. Its own `w5000.txt` gives 1.06
near `x = 1.07`, so the plan's table entry at `x = 1` appears to be the sum, not the
composite.

**New reading.** The same output lists the finite-`N` light exponent
`Lam~_N = Lambda^-_{k/mu_+}(m mu_- - j)` (the run count that keeps the plus runs
typical).

| x | `Lam~_N` at N = 5000 | `-log(B_N (P_N - G_N))` |
|---|---|---|
| 3 | 5.3 | 3.8 |
| 4 | 17.2 | 6.4 |
| 6 | 99 | 8.9 |

Beyond `x ~ 9` the light deviation is impossible: all minus runs would have length 1.

So for `x >= 4` the light term is negligible in this example. What `P - G` measures
there is the finite-size correction to the kernel. At `x = 20`, `L = 0.88N` lies in
the ballistic range, where `tau_N` overshoots `G_N` by 55%. The composite is then
worse than `G_N` alone (0.878 against 1.025).

The light/jump crossover in this example is near `x ~ 2.5`, where `Lam~_N` reaches
`-log(B_N G_N)`. This matches the composite's dip at `x ~ 3-4`. **The plan's table
therefore does not test O2.** It does support the composite remark R1 as a
finite-size device on `x <= N/(K B_N)`.

### 7.3 The crossover (P3 passed; P4 partly)

`py -I o2_crossover.py 3000 1.8 1 0.1 0.01 0.001 0.0001` writes
`out_crossover_N3000_a1.8.txt`. Setup: equal indices 1.8, minus law zeta, plus law
`(1-w) delta_1 + w zeta`, so `theta_+` is small through the tail constant.

| w | theta_+ | x_c (P = 2G) | x* (`Lam~ = -log BG`) | x_c/x* | `-log B(P-G)` / `Lam~` at x ~ 3 |
|---|---|---|---|---|---|
| 0.1 | 0.289 | 3.79 | 2.79 | 1.36 | 0.715 |
| 0.01 | 0.090 | 3.64 | 3.13 | 1.16 | 0.914 |
| 0.001 | 0.032 | 3.71 | 3.45 | 1.08 | 0.999 |
| 0.0001 | 0.030 | 3.87 | 3.71 | 1.04 | 1.010 |

- **P3 passed.** The light exponent ratio is in `[0.7, 1.3]` and moves to 1 as the
  big-jump term shrinks.
- **P4 partly.**
  - `x_c/x*` stays in `[0.6, 1.4]` and tends to 1. This is the content of Theorem
    O2(c), with the intrinsic `x*`.
  - My prediction that `x_c` increases with `log(1/theta_+)` **failed**: `x_c` stays
    near 3.6–3.9. The reason is the same wall. At `N = 3000`,
    `d/m = (x/p)B_N s/N` is not small, and `Lam~_N` grows far faster than
    `c_Z(x/p)^beta` (31.6 against 7.1 at `x = 5`). So the crossover is pinned by the
    finite-`N` exponent.
- For `w <= 0.001`, `b_{+,N}` falls to 1, so the printed `theta_+` is only nominal.

The asymptotic scale `(log 1/theta_+)^{(alpha_- - 1)/alpha_-}` cannot be seen at
computable `N`. Only the intrinsic, finite-`N` form `Lambda_N(x*) ~ -log(B_N G_N)`
is testable, and it is confirmed.

Run times: under 1 min for the table at `N = 5000`; about 15 min for the scan.
