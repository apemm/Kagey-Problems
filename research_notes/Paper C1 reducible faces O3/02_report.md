# Paper C1, item O3, part 2: the bridge face maxima in full, Theorem R(b) with a rate, and the crossing corollary

Date: 2026-10-25. This file continues `01_report.md`, which is left unchanged. It uses the
notation of its Section 2 and refers to its Lemma 2 (one bound for every block) and its part
(a). The paper is not edited.

## 0. Status

- Lemma D (the face maxima with the start and the end state fixed) is now proved in full,
  following `lem:discrete` and `thm:facemax` with `lem:local-general` in place of
  `thm:local`. Lemmas A to C come before it.
- Theorem R(b) is proved with the error `O(1/T + T^2/N)`, the rate of the irreducible case.
  The extra work is small: the continuum constants `A_j`, `B_j` are maxima of real-analytic
  functions that vanish at infinity, and the discrete blocks of bounded time are compared
  with the continuum with an additive error `O(h)`. Section 5.1 explains why the tails need
  no rate.
- The crossing formula is Corollary E, with its proof.
- Two things are still not written out in full. One is the extension of R(a) down to
  `T = 1` (remark in 01, Section 3). Theorem R' is stated from `T_1` on, so it does not need
  it. The other is the uniqueness of the order of the components, which is proved in 01,
  Section 2.

## 1. Notation (recap)

`F` is admissible, with components `C_1, ..., C_r` in the order of the paths. Put
`k_j = |C_j|`, `lambda_j = lambda_{C_j}` and `lambda_F = min_j lambda_j`. `k*` is the least
`k_j` with `lambda_j = lambda_F`, and `S* = {j : lambda_j = lambda_F, k_j = k*}`. Write
`a = (k*-1)/2`, `p_F = a + k_F - k*` and `X = N^{-(k_F-1)} T^{p_F} e^{-T lambda_F}
= h^{k_F-1} T^{-a} e^{-T lambda_F}`, with `h = T/N`. A block is *flat* if it is a singleton
`{i}` with `q_i = lambda_F`. Flat blocks exist only if `k* = 1`.

For an irreducible `C` with `|C| = k >= 2` and `y, x in C`, let `W_{yx}(m)` be the sum of
`prod_{j<M} q_{c_j c_{j+1}}` over the words `c` in `C` with `c_j != c_{j+1}`, `c_1 = y`,
`c_M = x` and `m_i` letters `i`. Put

    H_{yx}(t) = sum_{m in Z_{>=1}^C} W_{yx}(m) prod_i t_i^{m_i-1}/(m_i-1)!,      phi_{yx}(t) = e^{-<q,t>} H_{yx}(t).

This is `H_{A_C, e_y, e_x}` of `lem:torus-complex`. Since `W_{yx}(m) <= k^M q_max^{M-1}`,
the series converges absolutely for every `t in R^C`. So `H_{yx}` is entire, `phi_{yx}` is
real-analytic on all of `R^C`, and so is every series below obtained by multiplying the
terms by `M`, `M^2` or `2^M`. `phi_{yx} > 0` on `(0,oo)^C`, because `G_C` is strongly
connected and so some word from `y` to `x` uses every state. For `C = {i}` put
`phi(t) = e^{-q_i t}`. The `Phi_i` of 01 are the matrices `(phi_{yx})` of `C_i`.

For `alpha in Delta_C^o`, take `theta(alpha)`, `r_alpha`, `l_alpha` and `Sigma_alpha` from
`def:tilt` for the face `C`, so that `J_C(alpha) = <q - theta(alpha), alpha>`. Put

    c_{yx}(alpha) = r_{alpha,y} l_{alpha,x} / ( (2 pi)^{(k-1)/2} sqrt(det Sigma_alpha) ).

This does not depend on how `r_alpha` is scaled, since `l_alpha . r_alpha = 1`. It is
real-analytic and positive on `Delta_C^o` by `prop:constant`(a). At `alpha* = alpha*_C` it
equals `r_y l_x / ((2 pi)^{(k-1)/2} sqrt(det Sigma_C))`, with `r = r_C` and `l = l_C`
normalized by `l.r = 1`.

The chain is `I + hQ`, and `hq_max <= 1/2` throughout. For a composition `m` of `l` visits
on `C`, let `G(m)_{yx}` be the probability that the chain with `X_1 = y` has composition `m`
in `X_1, ..., X_l` and `X_l = x`.

## 2. Lemma A (the bridge run expansion)

For every `m in Z_{>=1}^C` with `|m| = l`, with `binom(n-1, m'-1) = 0` for `m' > n`,

    G(m)_{yx} = sum_{m' in Z_{>=1}^C} W_{yx}(m') h^{M'-1} prod_i binom(m_i - 1, m'_i - 1) (1 - h q_i)^{m_i - m'_i}.

*Proof.* The states of the maximal runs of a path that contributes form a word `c` with
`c_1 = y` and `c_M = x`. The path has probability `prod_j h q_{c_j c_{j+1}}` times
`(1 - hq_i)` for each of the `m_i - m'_i` stays in `i`. There are
`prod_i binom(m_i - 1, m'_i - 1)` paths with the word `c` and composition `m`, since `m_i`
splits into `m'_i` ordered positive run lengths. Sum over `c` (this is the proof of
`lem:runs` with the first and the last letter fixed, and `mu = e_y`). For a singleton,
`G(m) = (1 - hq_i)^{m-1}`.

With `t = hm`, write the `m'`-th term as `kappa_{m'} v_{m'}`, where

    v_{m'} = W_{yx}(m') h^{k-1} prod_i e^{-q_i t_i} t_i^{m'_i-1}/(m'_i-1)!,    sum_{m'} v_{m'} = h^{k-1} phi_{yx}(t),

    kappa_{m'} = prod_i [ prod_{1<=j<m'_i} (1 - j/m_i) ] (1 - hq_i)^{m_i - m'_i} e^{h q_i m_i}.

This holds because `h^{m'_i-1} binom(m_i-1, m'_i-1)
= t_i^{m'_i-1}/(m'_i-1)! * prod_{j<m'_i}(1 - j/m_i)` and `h^{M'-1} = h^{k-1} prod_i h^{m'_i-1}`.

**Bounds on kappa** (the proof of `eq:A-kappa`, which does not involve the weights). Every
`m'` has

    1 - sum_i m'_i (m'_i - 1)/(2 m_i) - q_max^2 h |t|  <=  kappa_{m'}  <=  e^{h q_max M'}.          (2.1)

*Proof.* If `m'_i <= m_i` for all `i`: each factor `1 - j/m_i` lies in `[0,1]` and
`(1 - hq_i)^{m_i - m'_i} <= e^{-hq_i(m_i - m'_i)}`, which gives the upper bound. For the lower
bound, `1 - prod_i b_i <= sum_i (1 - b_i)` for `b_i in [0,1]` gives
`prod_{i,j}(1 - j/m_i) >= 1 - sum_i m'_i(m'_i - 1)/(2m_i)`. Also
`log(1-x) >= -x - x^2` for `0 <= x <= 1/2` gives
`(1 - hq_i)^{m_i - m'_i} e^{hq_i m_i} >= (1 - hq_i)^{m_i} e^{hq_i m_i} >= e^{-h^2 q_i^2 m_i}
= e^{-h q_i^2 t_i}`. The product of these is at least `1 - q_max^2 h|t|`, and
`(1 - u)(1 - w) >= 1 - u - w` for `u, w >= 0`. If `m'_i > m_i` for some `i`, then
`kappa_{m'} = 0`, while `m'_i(m'_i - 1)/(2m_i) >= (m_i + 1)/2 >= 1`, so the left side is
`<= 0`.

## 3. Lemma B (blocks of bounded time)

For every `R` there is `C_R` such that, for `hq_max <= 1/2`, all `y, x` and every `m >= 1`
with `t = hm`, `|t| <= R`:

    | G(m)_{yx} / h^{k-1} - phi_{yx}(t) |  <=  C_R h,

and also `|(1 - hq_i)^{m-1} - e^{-q_i t}| <= C_R h` for a singleton.

*Proof.* Upper: by (2.1), `kappa_{m'} - 1 <= e^{hq_max M'} - 1 <= h q_max M' e^{M'/2}`,
using `h q_max <= 1/2`. So
`G/h^{k-1} - phi_{yx}(t) <= h q_max sum_{m'} W_{yx}(m') M' e^{M'/2}
prod_i t_i^{m'_i-1}/(m'_i-1)!`, and the sum is bounded on `|t| <= R` (Section 1).

Lower: by (2.1), `1 - kappa_{m'} <= sum_i m'_i(m'_i - 1)/(2m_i) + q_max^2 hR`. The term with
`i` vanishes unless `m'_i >= 2`, and `1/m_i = h/t_i`. So

    sum_{m'} v_{m'} m'_i(m'_i - 1)/(2 m_i) = h * h^{k-1} e^{-<q,t>} sum_{m'} W_{yx}(m') (m'_i/2) t_i^{m'_i-2}/(m'_i-2)! prod_{i' != i} t_{i'}^{m'_{i'}-1}/(m'_{i'}-1)!.

The last sum is bounded on `|t| <= R`. Summing over `i` gives
`phi_{yx}(t) - G/h^{k-1} <= C_R h`.

Singleton: `e^{-q t} e^{hq} >= (1 - hq)^{m-1} >= e^{-q t - q^2 h t}` gives the bound, with
`C_R = q_max e^{q_max/2} + q_max^2 R`.

**Corollary B'.** Let `D` be a finite product
`nu^T Psi_1 R_1 Psi_2 ... R_{i-1} Psi_i w` with fixed nonnegative `nu`, `R`'s and `w`. Each
`Psi` is either a block matrix `(G(m^(c))_{yx})/h^{k_c-1}` or a singleton factor. Let `D^c`
be the same product with `phi` in place of `G`, at the times `t^(c) = h m^(c)`. If
`sum_c |t^(c)| <= R`, then `|D - D^c| <= C'_R h`.

*Proof.* Telescope: `D - D^c` is a sum of products in which one factor is a difference,
bounded by `C_R h` entrywise by Lemma B. The other factors are bounded entrywise on
`|t| <= R`, by `sup phi` plus `C_R h`.

## 4. Lemma C (the bridge discrete law) and Lemma D (the bridge face maxima)

Fix an irreducible `C` with `k = |C| >= 2`.

**Lemma C.** Let `K` be a compact subset of `Delta_C^o`. Uniformly for `y, x in C`, `m` with
`m/l in K` and `1 <= s := hl <= l^{1/2}`,

    G(m)_{yx} = h^{k-1} phi_{yx}(hm) (1 + O_K(s^2/l)).

*Proof.* By Lemma A, `G(m)_{yx} / (h^{k-1} phi_{yx}(t)) = E_w kappa`, where `w` is the
probability `w_{m'} = v_{m'} / sum v`. It is well defined because `phi_{yx}(t) > 0`. Write
`alpha = m/l`, so that `t = s alpha`.

*Step 1. The number of runs.* For `sigma > 0` let `H^sigma_{yx}` be `H_{yx}` for the matrix
`sigma A_C`. A word with `M'` letters has `M' - 1` switches, so
`E_w sigma^{M'-1} = H^sigma_{yx}(t) / H_{yx}(t)`. The function
`Upsilon(c) = log E_w e^{c(M'-1)}` is finite and convex, with `Upsilon(0) = 0`, and
`Upsilon(1) >= 0` since `M' >= 1`. Hence `Upsilon(c) <= c Upsilon(1)` for `0 <= c <= 1`.

We show `Upsilon(1) <= C_K s`. Let `theta = theta(alpha)`. By `lem:local-general`, the
identities `eq:A-radii` hold for `A_C`: `theta > 0`,
`rho(A' - diag(theta')) < 0` and `g(theta') = theta_1`. These identities do not depend on
the weights. Let `X`, `g` and `b = b_{yx}` be the functions of `lem:torus-complex` for
`(A_C, e_y, e_x)`. Their series in `1/z_2, ..., 1/z_k` have nonnegative coefficients. The
functions for `(sigma A_C, e_y, e_x)` satisfy `X_sigma(sigma z') = sigma^{-1} X(z')`, so
`g_sigma(sigma z') = sigma g(z')` and `b_sigma(sigma z') = b(z')`. Take
`lem:torus-complex` for `sigma A_C` with the radii `sigma theta'`. On that torus,
`|g_sigma| <= sigma theta_1`, `|b_sigma| <= b(theta')` and `|z_i| = sigma theta_i`, so

    H^sigma_{yx}(t) <= sigma^{k-1} b(theta') prod_{i>=2} theta_i e^{sigma <t, theta>}.             (4.1)

On the other side, `lem:local-general` gives
`H_{yx}(s alpha) e^{-s<alpha,theta>} = (2 pi s)^{-(k-1)/2}
r_{alpha,y} l_{alpha,x} / sqrt(det Sigma_alpha) (1 + O_K(1/s))`. This is at least
`c_K s^{-(k-1)/2}` for `s >= s_1`. For `1 <= s <= s_1` the left side is continuous and
positive on `[1, s_1] x K`, so the same bound holds with a smaller `c_K`. Since `theta(alpha)`
and `b(theta'(alpha))` are bounded on `K` (`prop:constant`(a) and the continuity of `b`),
dividing (4.1) at `sigma = e` by this lower bound gives `Upsilon(1) <= C_K s`.

*Step 2. The two averages.* Let `u = h q_max <= 1/2`. Then
`E_w e^{u M'} = e^{u + Upsilon(u)} <= e^{u(1 + C_K s)} = 1 + O(hs) = 1 + O(s^2/l)`. Next, the
Chernoff bound gives `P_w(M' - 1 >= z) <= e^{Upsilon(1) - z}` for `z >= Upsilon(1)`, so

    E_w (M'-1)^2 = int_0^oo 2z P_w(M'-1 >= z) dz <= Upsilon(1)^2 + 2 Upsilon(1) + 2,

and therefore `E_w M'^2 = O(s^2)`.

*Step 3.* `m_i >= eps_K l`, with `eps_K = min_K min_i alpha_i`. By (2.1),
`kappa_{m'} >= 1 - M'^2/(2 eps_K l) - q_max^2 hs` and `kappa_{m'} <= e^{u M'}`. Taking
`E_w`, both bounds are `1 + O(s^2/l)`, since `hs = s^2/l`.

**Lemma D.** Let `lambda = lambda_C` and `alpha* = alpha*_C`. There are `s_2`, `l_2` and `C`
such that, for `y, x in C`, `hq_max <= 1/2`, `l >= l_2` and `s = hl in [s_2, l^{1/3}]`:

    (i)  max_{|m| = l} G(m)_{yx}  <=  Y_{yx} (1 + C(1/s + s^2/l)),
    (ii) G(m^0)_{yx}  >=  Y_{yx} (1 - C(1/s + s^2/l))   whenever |m^0_i - l alpha*_i| < 1 for all i,

where `Y_{yx} = h^{k-1} s^{-(k-1)/2} c_{yx}(alpha*) e^{-s lambda}`.

*Proof.* Coordinates and norms are those of Section `sec:secondorder`: `alpha' =
(alpha_2, ..., alpha_k)`, and `x = alpha' - alpha*'` is the displacement. Put
`J^0 = J_C - lambda`. It is nonnegative on `Delta_C` and vanishes only at `alpha*`
(`prop:variational`, `prop:rate`(a)).

*The ball.* `J_C` and `log c_{yx}` are real-analytic on `Delta_C^o`, with
`nabla^2 J_C = Sigma_alpha^{-1}` positive definite (`prop:constant`(a)), and `J^0` has a
critical point at `alpha*`. Taylor's theorem on a closed neighborhood of `alpha*` in
`Delta_C^o` gives `rho_0 > 0` and constants `c_U, C_U, C_1, C_3 > 0` with the following
properties. The set `K = {|x| <= rho_0}` lies in `Delta_C^o`, and on `K`, for all `y, x`:

    c_U |x|^2 <= J^0 <= C_U |x|^2,      | log(c_{yx}(alpha)/c_{yx}(alpha*)) - g_{yx} . x | <= C_1 |x|^2,

with `g_{yx} = nabla log c_{yx}(alpha*)` and `|g_{yx}| <= C_1`. Also `log c_{yx}` is
`C_3`-Lipschitz on `K`.

*Outside the ball.* The set `E = Delta_C \ {|x| < rho_0}` is compact. `J^0` is lower
semicontinuous on `E`, as a supremum of continuous functions, and positive there. So
`J^0 >= 3 eta` on `E` for some `eta > 0`. As shown before `lem:upper`,
`J_C(beta) = sup_{theta in V_C} <q - theta, beta>`. So each `beta in E` has some
`theta in V_C` with `<q - theta, beta> > lambda + 2 eta`, and by continuity the same `theta`
works on a neighborhood of `beta`. By compactness, finitely many `theta_1, ..., theta_p`
cover `E`.

Let `m/l in E`, and take `theta_j` that works at `m/l`. The bridge is at most the
probability that the chain started at `y` has composition `m` in its first `l` visits.
`lem:upper` with start `e_y` and `theta_j` (finitely many constants) bounds this by
`C h^{k-1} exp(-s <q - theta_j, m/l> + C h s)`. Since `hs = s^2/l <= 1`,

    G(m)_{yx} <= C h^{k-1} e^{-s(lambda + 2 eta)} = Y_{yx} * O(s^{(k-1)/2} e^{-2 eta s}).

*Inside the ball.* For `m/l in K`, Lemma C and `lem:local-general` with
`(nu, e) = (e_y, e_x)` at `t = s alpha` give

    G(m)_{yx} = h^{k-1} (2 pi s)^{-(k-1)/2} e^{-s J_C(alpha)} r_{alpha,y} l_{alpha,x} / sqrt(det Sigma_alpha) (1 + O(1/s))(1 + O(s^2/l))
              = Y_{yx} (c_{yx}(alpha)/c_{yx}(alpha*)) e^{-s J^0(alpha)} (1 + E),        |E| <= C_2 (1/s + s^2/l).      (4.2)

For `s >= 2C_1/c_U`, the logarithm of the two middle factors is at most
`g.x + C_1|x|^2 - c_U s|x|^2 <= g.x - (c_U s/2)|x|^2 <= |g|^2/(2 c_U s)`. So on `K`,
`G(m)_{yx} <= Y_{yx}(1 + O(1/s + s^2/l))`. Outside the ball the bound is smaller for `s`
large, which proves (i).

For (ii), `|x| <= k/l` at `m^0`. Then `c_{yx}(m^0/l) >= c_{yx}(alpha*) e^{-k C_3/l}` and
`s J^0(m^0/l) <= C_U k^2 s/l^2`, and (4.2) gives (ii). The uniformity in `y, x` holds because
there are finitely many pairs.

## 5. Theorem R' (Theorem R(b) with a rate)

**Theorem R'.** Let `F` be admissible, and let `K^red_F` be as in 01, Section 2. There are
`T_1`, `N_1` and `C` such that, for `N >= N_1` and `T_1 <= T <= N^{1/3}`,

    | M_F / X - K^red_F |  <=  C (1/T + T^2/N).

### 5.1 Two facts about the constant

For `j in S*`, define on the closed orthants the two functions

    F^<_j(t^<) = e^{lambda_F |t^<|} mu_{C_1}^T Phi_1(t^(1)) R_1 ... Phi_{j-1}(t^(j-1)) R_{j-1} r,
    F^>_j(t^>) = e^{lambda_F |t^>|} l^T R_j Phi_{j+1}(t^(j+1)) ... R_{r-1} Phi_r(t^(r)) 1,

with `r = r_{C_j}` and `l = l_{C_j}`, `l.r = 1`. By definition, `A_j = sup F^<_j` and
`B_j = sup F^>_j` over the open orthants.

(F1) *Regularity.* `F^<_j` and `F^>_j` are real-analytic on a neighborhood of the closed
orthants (Section 1), so they are Lipschitz on bounded sets, and the sups over the open
orthants equal the sups over the closed ones.

(F2) *Decay.* Let `w~_i(u)` be `e^{-(lambda_i - lambda_F)u}` if `lambda_i > lambda_F`,
`(1 v u)^{-(k_i-1)/2}` if `lambda_i = lambda_F` and `k_i >= 2`, and `1` for a flat block.
Then `e^{lambda_F |t^(i)|} Phi_i(t^(i))_{yx} <= C_0 w~_i(|t^(i)|)` entrywise.

*Proof of (F2).* Fix `t` in the open orthant and let `h -> 0` with `m = ceil(t/h)`. Lemma B
gives `G(m)/h^{k_i-1} -> Phi_i(t)`. Lemma 2 of 01 gives
`G(m) <= C_0 h^{k_i-1} w_i(h|m|)`, and `w_i` is continuous. By continuity the bound extends
to the closed orthant.

Consequences. Let `eta(R) = max(e^{-delta R/r}, (R/r)^{-1/2})`, where
`delta = min{lambda_i - lambda_F > 0}`. Then `eta(R) -> 0`. All factors are bounded by
`C_0`, and a non-flat factor whose block time is at least `u` is at most `C_0 eta(u r)`. If
`k* >= 2`, no block is flat. So `F^<_j(t^<) -> 0` as `|t^<| -> oo`, and likewise
`F^>_j`. By (F1) the sups `A_j` and `B_j` are attained, at points `t^<_*`, `t^>_*` of the
closed orthants. If `k* = 1`, the same holds after the flat blocks are dropped, because their
factors are identically 1.

The tails therefore need no rate. Section 5.2 handles a composition whose short blocks carry
a total time `rho >= R_0` by the crude bound `P <= C eta(R_0) X`, and this is `<= K X`
once `R_0` is fixed large. So only `rho <= R_0` needs the sharp estimate, and there every
error is `O(1/T + T^2/N + h)`. This is what was missing in 01, where `R` had to grow with
`T`.

### 5.2 Upper bound

Let `K = K^red_F`, and let `n` have support `F`. Write `s_i = hN_i`, so `sum_i s_i = T`. As
in 01, Section 4.6, set `a_j(n)^T = mu_{C_1}^T G_1 hR_1 ... G_{j-1} hR_{j-1}` and
`b_j(n) = hR_j G_{j+1} ... G_r 1`, so that `P_N(n) = a_j^T G_j(n^(j)) b_j` by (4.1) of 01.
All entries are nonnegative. By Lemma 2 of 01 and the arithmetic in its Section 4.3,

    P_N(n) <= C_1 h^{k_F-1} e^{-lambda_F T} prod_i w~_i(s_i).                          (5.1)

*Case `k* >= 2`.* Choose `j0` with `s_{j0} >= T/r`.

- (A) `j0` not in `S*`. Then `w~_{j0}(s_{j0}) <= max(e^{-delta T/r}, (T/r)^{-a-1/2})`, so
  `P_N(n) <= C X (T^a e^{-delta T/r} + T^{-1/2}) <= K X` for `T >= T_1`.
- (B1) `j0 = j in S*` and `rho := T - s_j >= R_0`. Some block `i != j` has `s_i >= R_0/r`,
  so `w~_i(s_i) <= eta(R_0)`, and `w~_j(s_j) <= (T/r)^{-a}`. By (5.1),
  `P_N(n) <= C_1 r^a eta(R_0) X`. Fix `R_0` with `C_1 r^a eta(R_0) <= K`.
- (B2) `j0 = j in S*` and `rho < R_0`. Then `s_j >= T - R_0`. Lemma D(i) applies to
  `C_j` with `l = N_j` and `s = s_j`: the range holds as in Lemma 2 of 01, since
  `s_j^3 <= l = s_j N/T` and `l >= N/(2T)`. It gives

      P_N(n) <= sum_{y,x} (a_j)_y G_j(n^(j))_{yx} (b_j)_x <= h^{k*-1} s_j^{-a} e^{-lambda_F s_j} (a_j.r)(l.b_j) / ((2pi)^a sqrt(det Sigma_{C_j})) (1 + C(1/T + T^2/N)),

  because `1/s_j <= 2/T` and `s_j^2/N_j = s_j T/N <= T^2/N`. The vector `a_j(n)/h^{kappa_<}`
  is a product as in Corollary B' with total time `rho_< <= R_0`. Here `kappa_<` is the
  number of factors `h` in `a_j`, namely `sum_{i<j}(k_i - 1) + (j-1)`. Corollary B' and the
  definition of `A_j` give `e^{lambda_F rho_<} a_j.r <= h^{kappa_<}(A_j + C h)`.
  Likewise `e^{lambda_F rho_>} l.b_j <= h^{kappa_>}(B_j + C h)`. Also
  `kappa_< + kappa_> + k* - 1 = k_F - 1`, `rho_< + rho_> + s_j = T` and
  `s_j^{-a} <= T^{-a}(1 + C R_0/T)`. Hence
  `P_N(n) <= X (A_j B_j/((2pi)^a sqrt(det Sigma_{C_j})) + C(1/T + T^2/N + h))
  <= X (K + C(1/T + T^2/N))`, since `h <= T^2/N` for `T >= 1`.

*Case `k* = 1`.* Let `rho` be the total time of the blocks that are not flat.

- If `rho >= R_0`, one of them has time `>= R_0/r`, and (5.1) gives
  `P_N(n) <= C_1 eta(R_0) X <= K X`.
- If `rho < R_0`, each flat block has `(1 - h lambda_F)^{N_i - 1} <= e^{h lambda_F}
  e^{-lambda_F s_i}`. The non-flat blocks form, between the flat ones, products as in
  Corollary B' with total time `<= R_0`. So
  `P_N(n) <= h^{k_F-1} e^{-lambda_F T} e^{r h q_max} (Psi* + C h)`. Here `Psi*` is the sup
  of the continuum product with every flat factor replaced by 1. Pick a flat `j in S*`. Its
  factor is 1, so the product splits into a left and a right part in disjoint variables, and
  `Psi* = A_j B_j = K`. So `P_N(n) <= X (K + C h)`.

In all cases `M_F <= X (K + C(1/T + T^2/N))`.

### 5.3 Lower bound

*Case `k* >= 2`.* Take `j in S*` with `A_j B_j / ((2pi)^a sqrt(det Sigma_{C_j})) = K`, and
the maximizers `t^<_*`, `t^>_*` of 5.1, with `|t^<_*| + |t^>_*| =: tau_*`. For every block
`i != j` put `n^(i) = max(1, ceil(t^(i)_*/h))` entrywise. Then
`|h n^(i) - t^(i)_*| <= h k_i`. By (F1), `F^<_j(h n^<) >= A_j - C h` and
`F^>_j(h n^>) >= B_j - C h`. Give block `j` the length `l = N - sum_{i != j} N_i`, so that
`s = hl = T - |hn^<| - |hn^>|`, which lies in `[T - tau_* - Ch, T - tau_*]`. Give it a
composition `m^0` with `|m^0_i - l alpha*_i| < 1` (it has full support for large `N`). By
Corollary B',

    a_j(n) >= h^{kappa_<} ( mu^T Phi_1 R_1 ... R_{j-1}(h n^<) - C h )   entrywise,

and similarly for `b_j`. Lemma D(ii) gives `G_j(m^0)_{yx} >= Y_{yx}(1 - C(1/T + T^2/N))`.
Since all entries are nonnegative,

    P_N(n) >= h^{k_F-1} s^{-a} e^{-lambda_F T} (F^<_j(hn^<) - Ch)(F^>_j(hn^>) - Ch) / ((2pi)^a sqrt(det Sigma_{C_j})) (1 - C(1/T + T^2/N)).

Finally `s^{-a} >= T^{-a}`, because `s <= T`. So `M_F >= P_N(n) >= X (K - C(1/T + T^2/N))`.

*Case `k* = 1`.* Use the same construction with a flat `j in S*`. Drop the flat factors from
the maximization, and give every flat block `i != j` the length 1. The block `j` has
`(1 - h lambda_F)^{l-1} >= e^{-lambda_F s - lambda_F^2 h s} >= e^{-lambda_F s}(1 - C T^2/N)`,
and the rest is as above.

Together with 5.2 this proves Theorem R'. QED

## 6. Corollary E (crossings with reducible faces)

**Corollary E.** Let `F` and `G` be admissible, with `Delta = k_F - k_G >= 1` and
`delta = lambda_G - lambda_F > 0`. Put `pi = p_F - p_G`, `kappa = log(K^red_F / K^red_G)`
and `D_N(T) = log M_F - log M_G`.

1. For large `N`, `D_N` has a zero in `[(Delta/2delta) L, (2Delta/delta) L]`.
2. For large `N`, every zero `T_N in [T_1, N^{1/3}]` satisfies
   `delta T_N + pi log T_N = Delta L - kappa + O(1/L)`.
3. All such zeros lie in one interval of length `O(1/L)`, and

       T_N = (Delta/delta) [ L - (pi/Delta) log L + b ] + O(log L / L),
       b = -(pi/Delta) log(Delta/delta) - kappa/Delta.

So the coefficient of `log log N` is `pi/Delta`. For irreducible `F` and `G` it is `1/2`,
which is Theorem `thm:crossing`. In `ex:threecycle`, `p_{1} = 0`, `p_{1,2} = 1` and
`p_{1,2,3} = 1`, which gives the coefficients `1` and `0`. Also `pi` can be negative: take
`F` irreducible with 4 states and `G` reducible with 3 states and `k*_G = 1`. Then
`pi = 3/2 - 2 = -1/2`.

*Proof.* `p_F = k_F - 1 - (k*_F - 1)/2` and `p_G` are fixed numbers. Subtract the logarithms
of Theorem R' for `G` from those for `F`. Uniformly on `[T_1, N^{1/3}]`,

    D_N(T) = -Delta L + Xi(T) + kappa + O(1/T + T^2/N),      Xi(T) = delta T + pi log T,      (6.1)

and by 01, Theorem R(a), the same holds with the error `O(1)`.

1. For fixed `N`, `M_F` and `M_G` are maxima of finitely many polynomials in `h`, and they
   are positive because the faces are admissible. So `D_N` is continuous in `T`. By (6.1),
   `D_N((Delta/2delta)L) = -(Delta/2)L + O(log L) < 0` and
   `D_N((2Delta/delta)L) = Delta L + O(log L) > 0`. So `D_N` has a zero in between.
2. First we locate a zero roughly. The `O(1)` form gives
   `delta T_N = Delta L - pi log T_N + O(1)`. If `pi >= 0`, then
   `T_N <= (Delta L + O(1))/delta`. If `pi < 0`, then
   `delta T_N <= Delta L + |pi| L/3 + O(1)`, since `T_N <= N^{1/3}`. Either way
   `T_N = O(L)`, so `log T_N = O(log L)` and `T_N = (Delta/delta) L + O(log L)`. In
   particular `T_N` is of order `L`, so the error in (6.1) is `O(1/L + L^2/N) = O(1/L)`,
   and `D_N(T_N) = 0` is the displayed equation.
3. Let `T°` solve `Xi(T°) = Delta L - kappa`. On `[cL, CL]`,
   `Xi'(T) = delta + pi/T >= delta/2` for large `N`. Every zero has
   `Xi(T_N) = Xi(T°) + O(1/L)`, so `|T_N - T°| = O(1/L)`. From
   `T° = (Delta/delta) L + O(log L)` we get
   `log T° = log L + log(Delta/delta) + O(log L/L)`. Putting this into
   `delta T° = Delta L - pi log T° - kappa` and dividing by `delta` gives the formula for
   `T_N`, with error `O(log L/L)`.

QED

## 7. Checks and what remains

- The numerics of 01 (Section 6) test exactly the constant of Theorem R'. Its four constants
  agree with exact `M_F` at `N = 20000` to within 0.25% after the fit in `1/T` and `T^2/N`.
  The residuals are of the size `1/T + T^2/N`, as R' predicts. The scripts are unchanged.
- For `ex:threecycle`, R' gives `K^red_{1,2} = b`, and Corollary E gives the paper's (ii) and
  (iii), including the constant term of (iii): the bracket constant is `-kappa = log b - log K_{1,2,3}` (here `b` is the rate `q_{12}`), with
  `Delta = 1`, `delta = 1` and `pi = 0`.
- What remains: (1) R(a) and R' are stated from `T_0` or `T_1` on. Extending them to
  `1 <= T` is the remark in 01, Section 3 (a compactness argument), which is not written out.
  It is not needed for Corollary E. (2) Lemma 2 of 01 uses `thm:facemax` with start `e_y`
  and `l` steps. The paper's constants depend on `(Q, mu)`, so the finitely many starts
  `e_y` are covered.
