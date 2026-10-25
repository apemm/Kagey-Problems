# Paper C1, item O3: face maxima on reducible faces

Date: 2026-10-25. Sources: `kagey-problems/problem131/paperC` (read only, not edited) and
item (O3) of `01_C1_plan_JTP.md`. Predictions were written first in `00_predictions.md`.

## 1. Status in one paragraph

The conjecture in the open questions of `sec_verify.tex` is true, with an explicit constant.
Part (a) below (two-sided bounds with the conjectured power of T, for
T_0 <= T <= N^{1/3}) is proved from results the paper already states: `thm:facemax`,
`thm:stratified`, `lem:upper` and Claim A of `app:first`. Part (b), the sharp constant, also
needs a bridge form of the face maxima (Lemma 4), meaning the start and end states are both
fixed. Its proof is the paper's proof of `lem:discrete` and `thm:facemax`, with
`lem:local-general` in place of `thm:local`. Section 4.4 lists the changes line by line, but
the full text of that check is not written out. The error term in (b) is only o(1). The rate
O(1/T + T^2/N) of the irreducible case is not proved here. Exact numerics on four reducible
faces, the reviewer's among them, confirm both the power and the constant (Section 6).

## 2. Setting

`F` is admissible, and `C_1, ..., C_r` are the strongly connected components of `G_F`. We
number them in the order of `lem:admissible`(a), so `mu(C_1) > 0` and some rate
`q_{xy} > 0` has `x in C_j`, `y in C_{j+1}`. Put `k_j = |C_j|`, `lambda_j = lambda_{C_j}`
and `lambda_F = min_j lambda_j` (Section `sec:notation`). Let `k*` be the least `k_j` with
`lambda_j = lambda_F`, and `S* = {j : lambda_j = lambda_F, k_j = k*}`. Then

    p_F = (k*-1)/2 + k_F - k*,      X_N(T) = N^{-(k_F-1)} T^{p_F} e^{-T lambda_F}.

Also `R_j = (q_{xy})_{x in C_j, y in C_{j+1}}` (nonzero), `h = T/N`, `L = log N`.

**The order is unique.** If a positive-probability path with support `F` leaves a component,
it never returns to it (proof of `lem:admissible`(a)). So the order of its blocks is a
Hamiltonian path in the condensation of `G_F`, which is acyclic. An acyclic digraph has at
most one Hamiltonian path, because such a path is a topological order and any two
consecutive vertices are joined by an edge, which forces the order. So every such path
visits `C_1, ..., C_r` in this order, each in one block of consecutive times.

**Bridge densities.** Let `C` be irreducible with `|C| >= 2`, let `y, x in C` and
`t in (0,oo)^C`. Put

    Phi_C(t)_{yx} = e^{-<q,t>} H_{A_C, e_y, e_x}(t)

with `H_{A,nu,e}` as defined before `lem:torus-complex`. As in the proof of `lem:continuum`,
this is the density of the occupation vector of the chain started at `y` on the event that it
stays in `C` during `[0,|t|]`, visits every state of `C` and ends at `x`. For `C = {i}` put
`Phi_C(t) = e^{-q_i t}`. Summing over `x`, with start `mu`, gives the density of
`lem:continuum`.

**The constant.** For `j in S*` let `r = r_{C_j}`, `l = l_{C_j}` with `l.r = 1`, let
`Sigma_{C_j}` be `Sigma_alpha` of `def:tilt` for the face `C_j` at `alpha*_{C_j}`, and write
`|t^{<}|`, `|t^{>}|` for the total time in the blocks before and after `j`. Define

    A_j = sup  e^{lambda_F |t^<|}  mu_{C_1}^T Phi_1(t^(1)) R_1 ... Phi_{j-1}(t^(j-1)) R_{j-1} r,
    B_j = sup  e^{lambda_F |t^>|}  l^T R_j Phi_{j+1}(t^(j+1)) R_{j+1} ... R_{r-1} Phi_r(t^(r)) 1,

with the sups over `t^(i) in (0,oo)^{C_i}`, `A_1 = mu_{C_1}.r` and `B_r = l.1`. Then

    K^red_F = max_{j in S*}  A_j B_j / ( (2 pi)^{(k*-1)/2} sqrt(det Sigma_{C_j}) ).

For `k* = 1` the denominator is 1 and `r = l = 1`. The product `A_j B_j` does not change
when `r` and `l` are rescaled. For `r = 1` (irreducible `F`), `K^red_F = K_F` of `def:tilt`.
`0 < K^red_F < oo` (Section 4.5).

## 3. The theorem

**Theorem R.** Fix `Q` and `mu`, and let `F` be admissible.

(a) There are `c, C > 0`, `T_0` and `N_0` such that `c X_N(T) <= M_F <= C X_N(T)` for
`N >= N_0` and `T_0 <= T <= N^{1/3}`.

(b) For every `eps > 0` there are `T_eps` and `N_eps` such that
`|M_F / X_N(T) - K^red_F| <= eps` for `N >= N_eps` and `T_eps <= T <= N^{1/3}`.

(c) If `F` is irreducible, (b) is `thm:facemax` with `v = 0` (up to the error rate).

Remarks.
- Theorem `thm:first`(ii) gave the powers `k_F - k*` and `k_F - 1`. (a) closes that gap at
  `p_F`, which is the conjecture.
- At a maximizer, the time `T - O(1)` goes to a component `j in S*`, near `alpha*_{C_j}`.
  Every other component gets time `O(1)` (it follows from the case analysis in 4.6).
- **Crossings.** For admissible `F`, `G` with `Delta = k_F - k_G >= 1` and
  `delta = lambda_G - lambda_F > 0`, (b) gives
  `D_N(T) = -Delta L + delta T + (p_F - p_G) log T + log(K^red_F/K^red_G) + o(1)` on
  `[cL, CL]`. So `T_N = (Delta/delta)[L - ((p_F-p_G)/Delta) log L + O(1)]`. The coefficient
  of `log log N` is `(p_F - p_G)/Delta`, which is `1/2` when both faces are irreducible. In
  `ex:threecycle`: `p_{1} = 0`, `p_{12} = 1` and `p_{123} = 1`. That gives the coefficients
  1 and 0 that the paper found by hand. Also `K^red_{12} = b` (from `A = b`, `B = 1`), which
  matches `M_{12} = bh(1-h)^{N-2}` exactly. With only o(1) in (b), the bracket is known up
  to o(1), not up to O(1/L).
- **Range down to T = 1.** (a) also holds for `1 <= T <= T_0`. There both sides are of order
  `N^{-(k_F-1)}`. The upper bound is in the proof of `thm:first`(ii). For the lower bound,
  take every block of length about `N/r`, and use Claim A with `hm` in a fixed compact subset
  of `(0, oo)`. Its proof applies unchanged.

## 4. Proof

### 4.1 Block factorization (exact)

For `n` with support `F` let `n^(j)` be its restriction to `C_j`, `N_j = |n^(j)|` and
`s_j = h N_j`, so `sum_j s_j = T`. Let
`G_j(m)_{yx} = P(X_1..X_{|m|} has composition m, X_{|m|} = x | X_1 = y)`, for the chain
`I + hQ`. Then

    P_N(n) = mu_{C_1}^T G_1(n^(1)) (h R_1) G_2(n^(2)) (h R_2) ... (h R_{r-1}) G_r(n^(r)) 1.     (4.1)

*Proof.* By Section 2, a path with composition `n` and positive probability has its j-th
block at the times `N_1+...+N_{j-1}+1, ..., N_1+...+N_j`, and these are fixed by `n`. The
Markov property at the `r-1` switches between blocks, summed over the switch states, gives
(4.1).

For a component `C_j` with `k_j >= 2`, the proof of `lem:runs` (with the words restricted to
start at `y` and end at `x`) gives the bridge run expansion

    G_j(m)_{yx} = sum_{m'} W_{yx}(m') h^{M'-1} prod_i C(m_i-1, m'_i-1)(1-hq_i)^{m_i-m'_i},

where `W_{yx} = W_{A_{C_j}, e_y, e_x}`. For `C_j = {i}`, `G_j(m) = (1-hq_i)^{m-1}`.

### 4.2 Lemma 2 (one bound for every block)

There is `C_0` such that, for `N >= N_0`, `T <= N^{1/3}`, every `j`, all `y, x in C_j` and every
composition `m` on `C_j` with `l = |m|`, `s = hl <= T`:

    G_j(m)_{yx} <= C_0 h^{k_j-1} w_j(s),

where `w_j(s) = e^{-lambda_j s}` if `lambda_j > lambda_F` or `k_j = 1`, and
`w_j(s) = (1 v s)^{-(k_j-1)/2} e^{-lambda_F s}` if `lambda_j = lambda_F` and `k_j >= 2`.

*Proof.* For `k_j = 1`: `(1-hq_i)^{l-1} <= e^{hq_i} e^{-q_i s} <= e^{1/2} e^{-lambda_j s}`.
For `k_j >= 2`: `G_j(m)_{yx}` is at most the probability that the chain started at `y` has
composition `m` in its first `l` visits. Apply `lem:upper` with start `e_y` and
`theta = q - lambda_j 1`, which lies in `V_{C_j}` since `A - diag(theta) = Q_{C_j} + lambda_j I`
has Perron root 0. This gives `C h^{k_j-1} e^{-lambda_j s + C h s}` with `hs <= T^2/N <= 1`.
If moreover `lambda_j = lambda_F` and `s >= 1`, apply `thm:facemax` (with `v = 0`) to the
chain started at `e_y`. Its face `C_j` satisfies (H). Use it with `l` steps in place of `N`
and `s` in place of `T` (the same `h`). The hypotheses hold: `l = sN/T >= N^{2/3} >= N_0`,
and `s^3 <= l` because it is the same as `s^2 T <= N`, which holds since `s <= T <= N^{1/3}`.
So the free-end probability, and hence `G_j(m)_{yx}`, is at most
`2 K l^{-(k_j-1)} s^{(k_j-1)/2} e^{-lambda_F s} = 2K h^{k_j-1} s^{-(k_j-1)/2} e^{-lambda_F s}`.
The starts `y` are finitely many.

### 4.3 Proof of (a)

*Upper bound.* By (4.1) and Lemma 2, summing over the finitely many switch states,
`P_N(n) <= C_1 h^{k_F-1} prod_j w_j(s_j)`, since `sum_j (k_j-1) + (r-1) = k_F - 1`. Write
`prod_j w_j(s_j) = e^{-lambda_F T} prod_j w~_j(s_j)` with all `w~_j <= 1`. Here
`w~_j(s) = e^{-(lambda_j-lambda_F)s}` or `(1 v s)^{-(k_j-1)/2}` (or `1` for a singleton with
`q_i = lambda_F`). Some `j0` has `s_{j0} >= T/r`. Let `delta = min{lambda_j - lambda_F > 0}`.
- If `lambda_{j0} > lambda_F`, then `w~_{j0} <= e^{-delta T/r}`.
- If `lambda_{j0} = lambda_F` and `k_{j0} >= 2`, then
  `w~_{j0} <= (T/r)^{-(k_{j0}-1)/2} <= r^{d} T^{-(k*-1)/2}`, since `k_{j0} >= k*`.
- If `lambda_{j0} = lambda_F` and `k_{j0} = 1`, then `k* = 1` and `T^{-(k*-1)/2} = 1`.

In all cases `P_N(n) <= C h^{k_F-1} T^{-(k*-1)/2} e^{-lambda_F T} = C X_N(T)`, because
`h^{k_F-1} = N^{-(k_F-1)} T^{k_F-1}` and `k_F - 1 - (k*-1)/2 = p_F`.

*Lemma 3 (a long bridge, lower bound).* Let `k* >= 2`, `j in S*`, `C = C_j`. There are `S_0`
and `c_3 > 0` such that for `N >= N_0`, `T <= N^{1/3}`, all `y, x in C` and every `l` with
`s = hl in [S_0, T]`:

    max { G(m)_{yx} : |m| = l, supp m = C }  >=  c_3 h^{k*-1} s^{-(k*-1)/2} e^{-lambda_F s}.

*Proof.* Let `m' = ceil(1/h)`, `l' = l - m'` and `s' = h l' in [s-2, s]`, and write
`alpha* = alpha*_C`. Let `W'` be the set of `n'` with `|n'| = l'` and
`|n'_i - l' alpha*_i| <= l' s'^{-1/2}/k*` for `i >= 2`. Then
`|n'_i/l' - alpha*_i| <= s'^{-1/2}` for every `i`, including `i = 1`, so for `S_0` large,
`n'/l'` lies in a fixed compact `K` inside `Delta_C^o`. Apply `thm:stratified` (or
`thm:local` with `lem:discrete`) to the chain started at `e_y`, with `l'` and `s'` in place of
`N` and `T`; the range holds as in Lemma 2. Since `J_C(alpha*) = lambda_F` and
`J_C - lambda_F <= C_U |alpha - alpha*|^2` on `K` (`prop:variational`, `prop:constant`(a);
`prop:restriction` identifies `J_V` with `J_C` on `Delta_C`), we get for `n' in W'`

    P_y(first l' visits have composition n') >= c h^{k*-1} s'^{-(k*-1)/2} e^{-lambda_F s'}.

Let `W = {n' + n'' : n' in W', |n''| = m'}`. Every `n in W` has `|n| = l` and full support.
A path of length `l` in `C` that ends at `x`, and whose first `l'` visits have composition
in `W'`, has composition in `W`, and different `n'` give disjoint events. So

    sum_{n in W} G(n)_{yx} >= sum_{n' in W'} sum_z P_y(n', X_{l'} = z) P_z(X_2..X_{m'+1} in C, X_{m'+1} = x)
                           >= c_A sum_{n' in W'} P_y(n'),

by Claim A of `app:first`. Its proof applies verbatim to `m'+1` visits, with `h(m'+1)` in
`[1,3]`. Counting coordinates `2..k*`:
`#W' >= (l' s'^{-1/2}/k*)^{k*-1}` and `#W <= (2 l' s'^{-1/2}/k* + m' + 1)^{k*-1}`. Since
`l' s'^{-1/2} = s'^{1/2}/h >= 1/h >= m' - 1`, the ratio `#W/#W'` is bounded. Hence
`max_{n in W} G(n)_{yx} >= (#W'/#W) c_A c h^{k*-1} s'^{-(k*-1)/2} e^{-lambda_F s'}`, and
`s' <= s` gives the claim.

*Lower bound in (a).* Take the switch states `y_1, x_j -> y_{j+1}` of `lem:admissible`(a)
and fix `j* in S*`. Let `m = ceil(N/T)`. Give each block `j != j*` the length `m`, and the
composition that maximizes `G_j(.)_{y_j x_j}` over compositions with full support. By Claim A
the total over these compositions is at least `c_A`, and there are at most
`(m+1)^{k_j-1} <= (3/h)^{k_j-1}` of them. So the maximum is at least `c h^{k_j-1}`. For a
singleton it is `(1-hq_i)^{m-1} >= e^{-4 q_max}`. Give block `j*` the length
`l = N - (r-1)m`, so `s = hl in [T - 2(r-1), T]`, and take the composition of Lemma 3 (or
`(1-h lambda_F)^{l-1} >= c e^{-lambda_F T}` if `k* = 1`). Here `T_0 = S_0 + 2r`. Keeping
one term of (4.1):

    M_F >= mu_{y_1} prod_{j<r} h q_{x_j y_{j+1}} prod_{j != j*} c h^{k_j-1} * c_3 h^{k*-1} T^{-(k*-1)/2} e^{-lambda_F T} >= c X_N(T).

This proves (a).

### 4.4 Lemma 4 (bridge face maxima) and Lemma 5 (short blocks)

**Lemma 4.** Let `k* >= 2`, `j in S*`, `C = C_j`, with `r`, `l`, `Sigma = Sigma_C` as in
Section 2. Put
`c_{yx}(alpha) = r_{alpha,y} l_{alpha,x} / ((2 pi)^{(k*-1)/2} sqrt(det Sigma_alpha))`, which
is real-analytic and positive on `Delta_C^o` (`prop:constant`(a); the product does not
depend on the normalization), and `c_{yx}(alpha*) = r_y l_x/((2 pi)^{(k*-1)/2} sqrt(det Sigma))`.
Uniformly for `y, x in C`, `T <= N^{1/3}` and `s = hl in [1, T]`:

(i) `max_{|m| = l} G(m)_{yx} <= h^{k*-1} s^{-(k*-1)/2} c_{yx}(alpha*) e^{-lambda_F s} (1 + O(1/s + s^2/l))`;

(ii) if `|m^0_i - l alpha*_i| < 1` for all `i`, then `G(m^0)_{yx}` is at least the same
main term times `(1 - O(1/s + s^2/l))`.

*Proof (by inspection of the paper's proofs).*
1. *Continuum.* `lem:local-general` with `(A, nu, e) = (A_C, e_y, e_x)` gives
   `e^{-<q,t>} H_{A_C,e_y,e_x}(t) = (2 pi s)^{-(k*-1)/2} e^{-s J_C(alpha)} r_{alpha,y} l_{alpha,x} / sqrt(det Sigma_alpha) (1 + O(1/s))`
   at `t = s alpha`, uniformly on compacts. It covers this weight because `e_y`, `e_x` are
   nonnegative and nonzero.
2. *Discrete.* `G(m)_{yx} = h^{k*-1} e^{-<q,t>} H_{A_C,e_y,e_x}(t) (1 + O(s^2/l))` for
   `m/l` in a compact and `1 <= s <= l^{1/2}`. The proof of `lem:discrete` goes through
   unchanged:
   - Step 1 compares the two sums term by term. The factors `kappa_m` do not involve the
     weights, and the bridge run expansion of 4.1 has the same binomials.
   - Step 2 (`eq:A-kappa`) is unchanged.
   - Step 3 needs an upper bound for `H_e` and a lower bound for `H`. The upper bound is
     `eq:A-Hsigma` with `b` for `(e_y, e_x)` (`lem:torus-complex`). The lower bound is step 1
     above for large `s`, and continuity and positivity on `[1, s_1] x K` otherwise.
     Positivity holds because `G_C` is strongly connected, so some word from `y` to `x`
     visits all of `C`.
   - Step 4 is unchanged.
3. *Maxima.* Repeat the proof of `thm:facemax` with `v = 0`, using `c_{yx}` in place of `C_F`.
   - Outside the ball `U`: the bridge is at most the free-end probability, which
     `lem:upper` bounds with finitely many `theta_j in V_C`.
   - Inside `U`: use steps 1 and 2. The quadratic bound and the point `n^0` are unchanged.
   - `J_C - lambda_F` vanishes only at `alpha*` (`prop:variational`).
   - The bounded-T paragraph is not needed (here `s >= T - R -> oo`).

   The range condition is the one checked in Lemma 2.

The only new inputs are the bridge weights. The paper already proves `lem:local-general` and
`lem:torus-complex` for general end vectors (for Section `sec:boundary-layer`). What is not
written out is the full text of steps 2 and 3. This is the one place where (b) rests on an
inspection rather than on a stated result.

**Lemma 5 (blocks of bounded time).** Let `sigma = e^{h q_max}`, and let `Phi^sigma_C` be
`Phi_C` with `A_C` replaced by `sigma A_C` (the diagonal `q` is kept).
(i) `G_C(m)_{yx} <= sigma h^{|C|-1} Phi^sigma_C(hm)_{yx}`. This is `eq:A-sigma` term by term
for the bridge words; for a singleton use `(1-hq)^{m-1} <= sigma e^{-q hm}`.
(ii) For fixed `t in (0,oo)^C` and `m = ceil(t/h)`, `G_C(m)_{yx}/h^{|C|-1} -> Phi_C(t)_{yx}`
as `h -> 0`. The terms converge one by one, and they are dominated by the terms of `(i)` with
`sigma <= 2` and `t + 1`, which are summable because `W(m) <= k^M q_max^{M-1}`.
(iii) For each `R`, `sup_{|t| <= R} |Phi^sigma_C(t) - Phi_C(t)| <= C_R (sigma - 1)` for
`1 <= sigma <= 2`. The `sigma`-derivative of the series is bounded on `|t| <= R` by the same
domination.

### 4.5 The constant is finite and positive

Letting `h -> 0` in Lemma 2, via Lemma 5(ii), gives `Phi_i(t)_{yx} <= C_0 w_i(|t|)`. So each
factor `e^{lambda_F |t^(i)|} Phi_i` is at most `C_0`, and `A_j`, `B_j` are finite. They are
positive because `mu(C_1) > 0`, every `R_i != 0`, `r, l > 0`, and `Phi_i > 0` on the open
orthant (`G_{C_i}` is strongly connected).

### 4.6 Proof of (b)

Write `a_j(n)^T = mu^T G_1 hR_1 ... G_{j-1} hR_{j-1}` and `b_j(n) = hR_j G_{j+1} ... G_r 1`,
so `P_N(n) = a_j^T G_j(n^(j)) b_j` for every `j`. All entries are nonnegative. Let
`eta(R) = max(e^{-delta R/r}, (R/r)^{-1/2}) -> 0`, and call a block *flat* if it is a
singleton with `q_i = lambda_F`.

*Upper bound, `k* >= 2`* (then no block is flat). Fix `n` with support `F` and `j0` with
`s_{j0} >= T/r`.
- *Case A,* `j0` not in `S*`. As in 4.3, `P_N(n) <= C X max(e^{-delta T/r}, T^{-1/2}) = o(X)`.
- *Case B1,* `j0 = j in S*` and `rho = T - s_j > R`. Some other block has `s_i >= R/r`, so
  `w~_i(s_i) <= eta(R)`, and `w~_j(s_j) <= (T/r)^{-(k*-1)/2}`. Hence
  `P_N(n) <= C r^{d} eta(R) X`.
- *Case B2,* `j0 = j in S*` and `rho <= R`. Then `s_j >= T - R`. By Lemma 4(i),
  `P_N(n) <= (1+o(1)) h^{k*-1} s_j^{-(k*-1)/2} e^{-lambda_F s_j} (a_j.r)(l.b_j) / ((2 pi)^{(k*-1)/2} sqrt(det Sigma))`.
  By Lemma 5(i) and (iii) on `|t| <= R`, `e^{lambda_F rho_<} a_j.r <= sigma^{r} h^{kappa_<} (A_j + C_R(sigma-1))`,
  where `kappa_<` is the number of factors `h` in `a_j`. Similarly for `l.b_j` with `B_j`.
  The exponentials combine to `e^{-lambda_F T}`, the powers of `h` to `h^{k_F-1}`, and
  `(T/s_j)^{(k*-1)/2} <= (T/(T-R))^{(k*-1)/2}`. So
  `P_N(n) <= X (A_j B_j/((2 pi)^{(k*-1)/2} sqrt(det Sigma)) + o(1)) <= X (K^red_F + o(1))`,
  with `o(1)` for fixed `R` as `T, N -> oo`. It collects `O(1/T + T^2/N)` from Lemma 4,
  `R/T`, and `sigma - 1 = O(N^{-2/3})`.

Choose `R` with `C r^d eta(R) <= K^red_F`, then `T, N` large. This gives
`M_F <= X (K^red_F + eps)`.

*Upper bound, `k* = 1`.* Let `rho_NF` be the total time of the blocks that are not flat.
- If `rho_NF > R`, some such block has time `>= R/r`, and `P_N(n) <= C eta(R) X` as in B1.
- If `rho_NF <= R`, bound each flat block by `(1-h lambda_F)^{N_i-1} <= sigma e^{-lambda_F s_i}`,
  and the other blocks by Lemma 5(i) and (iii). Then
  `P_N(n) <= sigma^{r} h^{k_F-1} e^{-lambda_F T} (Psi* + C_R(sigma-1))`. Here `Psi*` is the
  sup of the full continuum product, with every flat factor equal to 1. Since a flat `j` has
  factor 1, the product splits into a left and a right part, so `Psi* = A_j B_j = K^red_F`
  for any flat `j in S*`.

*Lower bound.* Take `j in S*` attaining the max and `eps > 0`. Choose interior `t^<`, `t^>`
within `eps` of the sups `A_j`, `B_j` (the sups are over open sets). Put
`n^(i) = ceil(t^(i)/h)` for `i != j`. Give block `j` the length
`l = N - sum_{i != j} N_i`, with `s = T - |t^<| - |t^>| + O(h)`, and the composition `m^0`
of Lemma 4(ii) (or the single state, if `k* = 1`). By Lemma 5(ii),
`a_j/h^{kappa_<} -> mu^T Phi_1 R_1 ... R_{j-1}` at `t^<`, and likewise for `b_j`. With
Lemma 4(ii) and nonnegativity,
`P_N(n) >= (1-o(1)) h^{k_F-1} s^{-(k*-1)/2} e^{-lambda_F T} (A_j - eps)(B_j - eps) / ((2 pi)^{(k*-1)/2} sqrt(det Sigma))`.
Since `s/T -> 1`, `M_F >= X (K^red_F - O(eps))`.

All error terms are uniform in `T_eps <= T <= N^{1/3}`, since `h <= N^{-2/3}` and
`T^2/N <= N^{-1/3}`. This proves (b). Part (c) holds since `r = 1` leaves only
`A_1 B_1 = (mu.r)(l.1)`. QED

## 5. Paper labels used

`lem:admissible`, `lem:runs`, `lem:continuum`, `eq:vertexmax`, `def:tilt`,
`prop:constant`(a), `prop:rate`, `prop:restriction`, `prop:variational`, `lem:upper` with
`eq:A-sigma` and `eq:A-Hsigma`, `lem:torus`, `lem:torus-complex`, `thm:local`,
`lem:local-general`, `lem:discrete` with `eq:A-kappa`, `thm:stratified`, `thm:facemax`,
`thm:first`(ii) with Claims A and B of `app:first`, `thm:crossing`, `ex:threecycle`, and the
open question in `sec_verify.tex`.

## 6. Numerics

All four faces have start `delta_1`. The predictions in `00_predictions.md` were fixed before
any code was run.

| case | face | k_F, k* | power predicted | K predicted |
|---|---|---|---|---|
| E1 (reviewer) | {1} -> {2,3}, q12=q23=q32=1 | 3, 2 | 1.5 | sqrt(2/pi) = 0.797885 |
| E2 | {1,2} -> {3}, q12=q21=q13=1, q34=2 | 3, 2 | 1.5 | 0.260705 |
| E3 | {1} -> {2,3} -> {4}, q12=q23=q32=q34=1, q45=3 | 4, 2 | 2.5 | 0.421830 |
| E4 | {1,2} -> {3,4}, both lambda=1 (tie) | 4, 2 | 2.5 | max(0.398942, 0.293525) |

Exact `M_F`, computed in double precision by (4.1) with one forward recursion per two-state
block, at `N = 20000` (`out_table_N20000.txt`):

| T | E1 slope, ratio/K | E2 slope, ratio/K | E3 slope, ratio/K | E4 slope, ratio/K |
|---|---|---|---|---|
| 4 | 1.5053, 0.9994 | 1.5517, 0.9736 | 2.4116, 1.0548 | 2.4441, 1.0444 |
| 8 | 1.5005, 1.0002 | 1.5159, 0.9891 | 2.4693, 1.0239 | 2.4724, 1.0190 |
| 15 | 1.5004, 1.0004 | 1.5070, 0.9946 | 2.4853, 1.0125 | 2.4820, 1.0067 |
| 25 | 1.5006, 1.0007 | 1.5019, 0.9963 | 2.4904, 1.0071 | 2.4729, 0.9948 |

A fit of `ratio = c0 + c1/T + c2 T^2/N` over `T >= 6` gives `c0/K = 1.0005, 1.0025, 0.9982, 0.9990`.

- Every slope tends to the predicted power and not to either bound of `thm:first`(ii), which
  are [1,2] for E1 and E2 and [2,3] for E3 and E4.
- E2 tests the end weight `l_1` of the bridge. The free-end weight `l.1` would give
  `K = 0.68`, which the data rule out.
- In E4 the maximizer puts time `T - 0.02` in `C1`, as predicted. The other candidate
  constant (0.2935) and the sum (0.69) are both ruled out.
- At `N = 4000` (`out_table_N4000.txt`) the `T^2/N` drift is visible for E4.
- The reviewer's 1.51 at `N = 500`, `T` from 2 to 7 matches our slopes 1.5187, 1.5053, 1.5015
  between `T = 2` and `T = 6`. That is the expected `O(1/T)` approach to 1.5.

The block engine agrees with an independent brute-force recursion over (state, visit counts)
for `N` up to 30, to within `5e-16` (`out_check.txt`). The constants were computed from
`def:tilt` (matrix `Z`, `Gamma`, `Sigma`) and agree with the hand values. The E4 continuum
sups are `B_1/l_1 = 1` (attained as `t -> 0`) and `A_2 = 1/e` (the boundary `t_2 -> 0`, with
`t_1 = 1`).

Commands (from this folder):

    py -I o3_check.py        > out_check.txt
    py -I o3_table.py 4000   > out_table_N4000.txt
    py -I o3_table.py 20000  > out_table_N20000.txt      (about 90 s)

## 7. What remains

1. Write out steps 2 and 3 of Lemma 4 in full. They are routine, but they are the only
   inspection step behind (b). Part (a) does not use them.
2. An error rate in (b). The proof gives o(1). When every other component has
   `lambda_i > lambda_F` and the sups are attained, it would give about
   `O(log T/T + T^2/N)` with `R = C log T`. A tie with another component (as in E4) gives
   only polynomial tails in `R`, so the proof gives a weaker rate. The numerics suggest
   `O(1/T + T^2/N)` in all four cases.
3. For the paper: (a) is short (about one page on top of `app:first`). (b) needs Lemmas 4
   and 5, about two more pages. The crossing corollary is one paragraph, and it explains
   the coefficients 1 and 0 of `ex:threecycle` in one formula.
