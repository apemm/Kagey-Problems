# Paper C1, item O2: the local law over the whole switching range

25 October 2026. Paper C1 is `kagey-problems/problem131/paperC` (problem131_chains.tex
and its sections, read as they stand in the working tree). Nothing in the paper was
edited. The plan is item (O2) of `01_C1_plan_JTP.md` in the 25 October upgrade
folder. Predictions were filed first in `00_predictions.md`. All scripts are in this
folder and run with `py -I`.

## 0. Status

**Proved below, in full apart from routine compactness checks that I list in
section 8:**
- the local law of Theorem A with exponent `N I_h(n/N)`, where `I_h` is the
  Donsker–Varadhan rate of `P = I + hQ`, and an explicit `h`-dependent constant
  `C_F^(h)`, with relative error `O(1/T)`. It holds uniformly for `1 <= T <= h_* N`,
  for every fixed `h_* < 1/q_max`. In particular it holds for any `epsilon N` with
  `epsilon q_max < 1`, which is more than the plan asks;
- the face maxima with `(1 - h lambda_F)^N` in place of `e^{-T lambda_F}`, the
  constant `K_F^(h)`, error `O(1/T)`, and every maximizer within `O(1/T)` of the
  same quasi-ergodic law `alpha*_F` for every `h`.

The error no longer contains `T^2/N`.

**Route.** The plan's route works, and it is short. Good's discrete formula
(Lemma `lem:runs`) has an exact torus representation of the same shape as
Lemma `lem:torus`, with `e^{t_i z_i}` replaced by `(1 - h q_i + h z_i)^{n_i - 1}`. In
the variable `z`, every object is real-analytic in `h` on `[0, h_*]`, including
`h = 0`, where it is the continuum object. So Laplace's lemma with the compact
parameter set `[0, h_*] x K` gives uniformity in `h` at no extra cost. No comparison
with the continuum is made.

**Numerics.**
- The plan's table is reproduced exactly on its 9-point grid.
- With the new constant, the full local law holds with `T |R - 1| <= 0.2` from
  `T = 16` to `T = 1000 = N/4`.
- A proper face with an exit rate matches the new face maximum to `5e-4` at every
  `T` up to `N/4`.
- A non-reversible three-state chain matches the `k = 3` law.

**Novelty.** No source states a local law, or even exact large deviations, that is
uniform as `I + hQ -> I` (section 7).

## 1. The theorem

The notation is C1's (sec_model, sec_dv, sec_secondorder, app_torus). Write
`p_i = 1 - h q_i`, fix `h_*` with `h_* q_max < 1`, and put
`p_min = 1 - h_* q_max > 0`. For `h > 0`, the discrete Donsker–Varadhan rate of
`P = I + hQ` on `[d]` is

    I_h(alpha) = sup_{u in (0,inf)^d} sum_i alpha_i log( u_i / (P u)_i ),

and we put `J_h = I_h / h`, so that `N I_h(n/N) = T J_h(n/N)`. With `theta = A_F u / u`,
which runs over `V_F` (sec_firstorder), and `L_h(y) = -log(1 - h y)/h`, we have, for
`alpha in Delta_F`,

    J_h(alpha) = sup_{theta in V_F} sum_{i in F} alpha_i L_h(q_i - theta_i),        (1.1)

the exact discrete analogue of `J_F(alpha) = sup_theta <q - theta, alpha>`. We set
`J_0 = J_F`.

**Definition (discrete tilt and constant).** Let `F` be irreducible with `k >= 2`, and
let `alpha in Delta_F^o` and `h in [0, h_*]`.
- `theta^h(alpha)` is the maximizer in (1.1). It exists and is unique by Lemma D1.
- `r, l` are the positive null vectors of `A_F - diag theta^h(alpha)`, with `l.r = 1`,
  and `pi = l o r`.
- `c_h(alpha) = sum_i alpha_i / (p_i + h theta^h_i)`.
- The constant is

      C_F^(h)(alpha) = c_h(alpha) (mu.r)(l.1) sqrt( det Hess J_h(alpha) / (2 pi)^(k-1) ),

  with the Hessian taken in the coordinates `alpha_2..alpha_k`.
- Equivalently (Lemma D1(e)),
  `C_F^(h) = b(theta') / ((2 pi)^((k-1)/2) prod_{i in F}(p_i + h theta_i) sqrt(det H_h))`,
  where `b` is from Lemma `lem:torus` and `H_h` is the Hessian in (3.1).
- At `h = 0`, `c_0 = 1` and `C_F^(0) = C_F` (Proposition `prop:constant`(a)).
- `C_F^(h)(alpha)` is real-analytic and positive on `[0, h_*] x Delta_F^o`, so
  `C_F^(h) = C_F (1 + O(h))` on compacts.
- For a field `v`, put
  `lambda_F^(h)(v) = -(1/h) log rho((I + h Q_F) e^{h diag v})`. Let `alpha^{*,h}_F(v)` be
  the unique minimizer of `J_h - v.alpha` on `Delta_F` (Lemma D2), and
  `K_F^(h)(v) = C_F^(h)(alpha^{*,h}_F(v))`.
- At `v = 0`: `lambda_F^(h) = -(1/h) log(1 - h lambda_F)`, `alpha^{*,h}_F = alpha*_F` for
  every `h`, and `K_F^(h) = K_F^(h)(0)`. For a singleton put
  `K_{i}^(h) = mu_i / (1 - h q_i)`.

**Theorem A_h (the law on a face over the whole switching range).** Fix `Q`, `mu`
and `h_* < 1/q_max`. Let `F` satisfy (H), with `k = |F| >= 2`, and let
`K ⊂ Delta_F^o` be compact.

(a) *Local law.* There are `N_0` and `C` such that for `N >= N_0`, `1 <= T <= h_* N`
(so `h in [1/N, h_*]`), and `supp n = F` with `n/N in K`,

    P_N(n) = N^-(k-1) T^((k-1)/2) C_F^(h)(n/N) e^{-N I_h(n/N)} (1 + E),   |E| <= C/T,

equivalently

    -log P_N(n) = (k-1) log N + N I_h(n/N) - (k-1)/2 log T - log C_F^(h)(n/N) + O(1/T).

Here `I_h` may be read as the rate of the full chain on `[d]`, since `I_h^V = I_h^F` on
`Delta_F` (Lemma D1(a)).

(b) *Face maxima.* Let `V ⊂ R^d` be compact. Uniformly for `v in V` and
`1 <= T <= h_* N`,

    M_F(T, v) = N^-(k-1) T^((k-1)/2) K_F^(h)(v) e^{-T lambda_F^(h)(v)} (1 + O(1/T)),

and every maximizer `n̂` has `n̂/N = alpha^{*,h}_F(v) + O(1/T)`. At `v = 0`:

    M_F = N^-(k-1) T^((k-1)/2) K_F^(h) (1 - h lambda_F)^N (1 + O(1/T)),
    n̂/N = alpha*_F + O(1/T).

For `k = 1`, `M_{i} = mu_i (1 - h q_i)^(N-1) = K_{i}^(h) (1 - h q_i)^N` exactly.

(c) *Comparison with Theorem A.* Uniformly on `K`, with `theta = theta(alpha)` the
continuum tilt,

    N I_h(alpha) = T J_V(alpha) + (T^2/(2N)) sum_i alpha_i (q_i - theta_i(alpha))^2 + O(T^3/N^2),
    -N log(1 - h lambda_F) = T lambda_F + T^2 lambda_F^2/(2N) + O(T^3/N^2),
    C_F^(h) = C_F (1 + O(T/N)).

So (a) and (b) give back Theorem A (`thm:A` = `thm:stratified` + `thm:facemax`) for
`T <= N^{1/2}`. The `T^2/N` in Theorem A is exactly this second-order term, so it
cannot be removed while the exponent stays `T J_V` (except where
`alpha -> sum alpha_i (q_i - theta_i)^2` is constant on `K`, or `lambda_F = 0` for the
maxima).

*Remarks.*
- Note `K_F^(h)` contains the factor `c_h(alpha*_F) = 1/(1 - h lambda_F)`. This is the
  same factor that makes the singleton formula `mu_i (1 - h q_i)^(N-1)` fit the
  pattern `K^(h) (1 - h lambda)^N`.
- The maximizer location `alpha*_F` does not move with `h`, because `I + hQ_F` and
  `Q_F` have the same Perron vectors.

## 2. The discrete rate: two lemmas

Throughout, `F` is irreducible with `k >= 2`, `h in [0, h_*]`, and
`L_h(y) = int_0^1 y ds/(1 - s h y)`, so that `L_0(y) = y`. For
`psi in R^F`, let `theta_i(psi) = sum_{j in F} q_ij e^{psi_j - psi_i}` and

    G_h(alpha, psi) = sum_i alpha_i L_h(q_i - theta_i(psi)).

Since `1 - s h (q_i - theta_i) >= 1 - h q_i >= p_min`, `G` is real-analytic near
`[0, h_*] x Delta_F^o x R^F`. For `h > 0`,
`L_h(q_i - theta_i(psi)) = -(1/h) log((P_F u)_i / u_i)` with `u = e^psi`. So
`J_h = sup_psi G_h(alpha, ·)` agrees with (1.1) and with `I_h^F / h`.

**Lemma D1.**
(a) For `alpha in Delta_F`, `I_h^V(alpha) = I_h^F(alpha)` (the restriction identity in
discrete time).

(b) For each `(h, alpha) in [0, h_*] x Delta_F^o`, `G_h(alpha, ·)` is strictly concave
modulo constants, with a Hessian that is negative definite on `{psi_1 = 0}`, and it
tends to `-inf` at infinity. Its maximizer `psi^h(alpha)` (with `psi_1 = 0`) is
unique and real-analytic in `(h, alpha)`. Hence `theta^h(alpha) = theta(psi^h(alpha))`
lies in `V_F`, and `J_h(alpha) = sum_i alpha_i L_h(q_i - theta^h_i)` is real-analytic.

(c) `theta in V_F` equals `theta^h(alpha)` if and only if
`alpha_i / (p_i + h theta_i)` is proportional to `pi_i(theta)`, where `pi(theta) = l o r` for
`A_F - diag theta`. So `theta^h(alpha) = theta(alpha~)`, where `alpha~` is the continuum
tilt at `alpha~ = (alpha_i/(p_i + h theta_i))_i / c_h`.

(d) Let `Omega = {s' : rho(A' - diag s') < 0}` and
`Psi_h(alpha; s') = sum_i alpha_i ell_h(s_i - q_i)`, where `s_1 = g(s')` and
`ell_h(x) = log(1 + h x)/h`. Then `theta^h(alpha)'` is the unique minimizer of
`Psi_h(alpha; ·)` on `Omega`, it is nondegenerate, and the Hessian
`H_h = Hess_{s'} Psi_h(alpha; theta')` is positive definite. Moreover
`Hess J_h(alpha) = K^T H_h^{-1} K`, with
`det K = 1/(c_h pi_1 prod_i(p_i + h theta_i))`. So `Hess J_h` is positive definite, and it
equals `Sigma_alpha^{-1}` at `h = 0`.

(e) `b(theta') / (prod_i(p_i + h theta_i) sqrt(det H_h)) = c_h (mu.r)(l.1) sqrt(det Hess J_h)`.
So the two forms of `C_F^(h)` agree.

*Proof.*

(a) This is the proof of Proposition `prop:restriction`. For `j` not in `F` the terms
`h q_ij u_j` in `(P u)_i` only increase `(P u)_i`, and they tend to 0 as
`u_j -> 0`.

(b) At `h = 0` this is Proposition `prop:rate`(b). In direction `delta`, the Hessian
of `-theta_i` is `-sum_j q_ij e^{psi_j - psi_i}(delta_j - delta_i)^2`, which vanishes
for all `i` only if `delta` is constant, by strong connectivity.

For `h > 0`,
`-G_h = (1/h) sum_i alpha_i log(p_i e^0 + sum_j h q_ij e^{psi_j - psi_i})`, a sum of
log-sum-exp functions of the affine forms `0` and `psi_j - psi_i`. In direction
`delta`, the Hessian of the `i`-th term is the variance, under the weights
proportional to `p_i` and `h q_ij e^{psi_j - psi_i}`, of a variable that takes the
values `0` and `delta_j - delta_i`. Since `p_i >= p_min > 0`, this variance vanishes
only if `delta_j = delta_i` on every edge out of `i`. Summing over `i` shows that the
Hessian vanishes only for constant `delta`. This is where `h_* q_max < 1` is used.

Coercivity is the argument of `prop:rate`(b). Let `a` be the least positive rate.
Some edge `i -> j` has `psi_j - psi_i >= psī/(k-1)`, so that term is at most
`alpha_i L_h(q_i - a e^{psī/(k-1)}) -> -inf`. The other terms are at most
`L_h(q_max) <= q_max / p_min`.

The maximizer is a critical point with an invertible Hessian, and `G` is analytic
near `(h, alpha, psi)`, including `h = 0`. So the implicit function theorem gives local
analyticity, and uniqueness makes the local branches agree.

(c) Put `w_i = alpha_i L_h'(q_i - theta_i) = alpha_i/(p_i + h theta_i)`. Then
`d G / d psi_m = -sum_i w_i (d theta_i / d psi_m)`. This is the continuum gradient with
`alpha` replaced by `w`. By `eq:stationary` and the criterion in `prop:rate`, it
vanishes if and only if `w` is proportional to the stationary law of
`R^{-1}(A_F - diag theta) R`, namely `l o r`.

(d) The map `s' -> (g(s'), s')` is a bijection from `Omega` onto `V_F`: see
`eq:A-radii`, and conversely `lambda(g(z'), z') = 0` in the proof of `thm:local`. The
map `psi -> theta(psi)'` from `{psi_1 = 0}` onto `Omega` is an analytic diffeomorphism,
with inverse the log of the normalized Perron vector. Also
`-Psi_h(alpha; theta(psi)') = G_h(alpha, psi)`. So the minimizer is unique and
nondegenerate, and at a critical point the two Hessians are congruent, which makes
`H_h` positive definite.

For the Hessian of `J_h`, write `y_i = ell_h(s_i - q_i)`, so that
`Psi_h = y_1 + sum_{j>=2} alpha_j (y_j - y_1)` and `J_h(alpha) = -Psi_h(alpha; theta'(alpha))`.
By the envelope theorem, `d J_h / d alpha_j = -(y_j - y_1)`. Differentiating the
critical-point equation in `alpha` gives
`d theta'/d alpha' = -H_h^{-1} K`, with `K_ij = d(y_j - y_1)/d s_i`. Hence
`Hess J_h = K^T H_h^{-1} K`.

Next we compute `K`. With `e_j = 1/(p_j + h theta_j)` and `g_i = -pi_i/pi_1` (the identity
`g_j = -alpha_j/alpha_1` of app_torus, applied at the continuum point whose law is
`pi`), we get `K = diag(e') + (e_1/pi_1) pi' 1^T`. The matrix determinant lemma gives
`det K = prod_i e_i * sum_i pi_i (p_i + h theta_i) / pi_1`. By (c),
`alpha_i = c_h pi_i (p_i + h theta_i)`, so `sum_i pi_i (p_i + h theta_i) = 1/c_h`.

(e) The identity `alpha_1 b(theta') = (mu.r_alpha)(l_alpha.1)` of `lem:local-general`,
applied at the continuum point `pi`, gives `b(theta') = (mu.r)(l.1)/pi_1` with
`l.r = 1`. By (d), `1/sqrt(det H_h) = sqrt(det Hess J_h) / |det K|`. Combining the
two gives (e). ∎

**Lemma D2 (minimum on a face).** For `v in R^F`, put
`M = e^{h diag v} P_F = e^{h diag v}(I + h Q_F)`. Then:
- `min_{Delta_F}(J_h - v.alpha) = lambda_F^(h)(v) = -(1/h) log rho(M)`, and the minimum
  is attained only at `alpha^{*,h}_F(v) in Delta_F^o`, which is `l o r` normalized for
  the Perron vectors of `M`;
- on a proper subface `F'`, `J_h - v.alpha >= lambda_{F'}^(h)(v) > lambda_F^(h)(v)`;
- at `v = 0`, `rho(M) = 1 - h lambda_F` and `alpha^{*,h}_F = alpha*_F`;
- `lambda_F^(h)(v)` and `alpha^{*,h}_F(v)` are real-analytic in `(h, v)` on
  `[0, h_*] x R^F`, and at `h = 0` they are `lambda_F(v)` and `alpha*_F(v)`.

*Proof.*
- *Lower bound.* `J_h - v.alpha = (1/h) sup_u sum alpha_i log(u_i/(M u)_i)`. With
  `u = (s - M)^{-1} 1` and `s > rho(M)`, every ratio `u_i/(M u)_i` exceeds `1/s`. Let
  `s` decrease to `rho(M)`. This also works on reducible subfaces, as in
  `prop:rate`.
- *Equality.* With `u = r(M)`, every ratio equals `1/rho(M)`. That `u` is optimal for
  `alpha` exactly when `alpha` is stationary for the tilted stochastic matrix
  `M_ij r_j/(rho r_i)`, that is, `alpha = l o r`, by the criterion of (c).
- *Uniqueness.* In the interior, uniqueness follows from strict convexity
  (Lemma D1(d)). On the boundary, use D1(a) and strict Perron monotonicity, as in
  `lem:face-monotone`: the padded principal submatrix of the irreducible `M` is `<= M`
  and not equal to it.
- *The case `v = 0`.* `I + h Q_F` has the Perron vectors `r_F, l_F` of `Q_F` and Perron
  root `1 - h lambda_F`.
- *Analyticity at `h = 0`.* `rho(M) = 1 - h lambda_F(v) + O(h^2)` is a simple
  eigenvalue, analytic in `(h, v)`, and the same holds for `-(1/h) log rho(M)`. ∎

## 3. The discrete torus representation

**Lemma T_h.** Let `hq_max <= 1`, `supp n = F`, and let `s'` satisfy
`rho(A' - diag s') < 0`. With `g`, `b` as in `lem:torus` and `z_i = s_i e^{i phi_i}`,

    P_N(n) = h^(k-1) (2 pi)^-(k-1) int_{T^(k-1)} (p_1 + h g(z'))^(n_1 - 1)
             prod_{i>=2} (p_i + h z_i)^(n_i - 1) b(z') prod_{i>=2} z_i dphi.      (3.1)

*Proof.* Follow the proof of `lem:torus` step by step, with one change in Step 3:
the Cauchy identity

    (1/2 pi) int (p + h z)^(n-1) z^(1-m) dphi = h^(m-1) C(n-1, m-1) p^(n-m)   (m >= 1),

which is `0` for `m <= 0`, replaces `t^{m-1}/(m-1)!`. It is the coefficient of
`z^{m-1}` in the binomial expansion. It vanishes automatically for `m > n`, since the
polynomial has degree `n - 1`.

Multiply the word series of `mu^T(Z - A_F)^{-1} 1` (absolutely and uniformly
convergent on the torus, Step 3) by `prod_i (p_i + h z_i)^(n_i - 1) z_i` and integrate
term by term. The result is
`sum_m W(m) prod_i h^(m_i - 1) C(n_i - 1, m_i - 1) p_i^(n_i - m_i)`. Multiplied by
`h^(k-1)`, this is Lemma `lem:runs`, since `h^(M-1) = h^(k-1) prod_i h^(m_i - 1)`.

Step 4 is unchanged. The second block term gives `int poly(z_1) z_1 dphi_1 = 0`. The
first gives the value of the polynomial `(p_1 + h z_1)^(n_1 - 1)` at `z_1 = g(z')`, by
Cauchy's formula on any circle `|z_1| = s_1 > g(s') >= |g(z')|`. ∎

**Corollary U_h (an exact discrete Chernoff bound; replaces `lem:upper`).** For
every `theta in V_F`, every `n` with `supp n = F` (of any length `|n|`), every `h` with
`hq_max <= 1` and every `v`,

    P_{|n|}(n) e^{h<v,n>} <= h^(k-1) b(theta') prod_{i>=2} theta_i prod_i (p_i + h theta_i)^(n_i - 1) e^{h v_i n_i}.

*Proof.* Take `s' = theta'`, which is allowed by `eq:A-radii`, and bound the integrand
by its modulus. This uses `|p_i + h z_i| <= p_i + h theta_i`, and
`|p_1 + h g(z')| <= p_1 + h theta_1` by `|g(z')| <= g(theta') = theta_1`. ∎

Compared with Lemma `lem:upper`, the factor `exp(C h^2 |n|)` is gone. It came only
from comparing the discrete sum with the continuum sum `H_sigma`.

## 4. Proof of Theorem A_h(a)

Let `P = [0, h_*] x K`, a compact set. For `(h, alpha) in P`, take the radii
`s' = theta'`, where `theta = theta^h(alpha)` (Lemma D1). On the torus put
`Psi_h(alpha, phi) = sum_i alpha_i ell_h(z_i - q_i)`, with `z_1 = g(z')` and the principal
logarithm, and

    a_h(alpha, phi) = b(z') prod_{i>=2} z_i / prod_i (p_i + h z_i).

Since `n_i = T alpha_i / h`, we have `prod_i (p_i + h z_i)^(n_i - 1) = e^{T Psi_h} a_h / (b prod z)`
wherever the logarithms are defined. So (3.1) reads

    P_N(n) = h^(k-1) (2 pi)^-(k-1) int e^{T Psi_h(alpha,phi)} a_h(alpha, phi) dphi.

At `h = 0`, `(Psi_0, a_0)` are the `(Psi, chi)` of `eq:A-fT`. They are used only as the
end point of the compact parameter set, not as a law.

*Regularity on a cube.* `theta^h(alpha)` is continuous on `P`, so
`theta_i in [theta_min, theta_max]` with `theta_min > 0`, and `rho(A' - diag theta')`
stays below a negative constant. As in the regularity paragraph of the proof of
`thm:local`, there are `delta > 0` and `eps_1 > 0` such that on
`{||phi|| <= eps_1}`:
- `X`, `g` and `b` are holomorphic;
- `Re(p_i + h z_i) >= p_min/2` and `Re(p_1 + h g(z')) >= p_min/2`.

Here `ell_h(x) = int_0^1 x ds/(1 + s h x)` is analytic in `(h, x)` on
`{Re(1 + h x) > 0}`, including `h = 0`. Hence `Psi_h` and `a_h` are real-analytic in
`(h, alpha, phi)` on `P x {||phi|| <= eps_1}`. So their `phi`-derivatives up to orders
4 and 2 are bounded there, by constants `B_Psi` and `B_a`.

*Hypotheses (i) and (ii) of `lem:laplace`.*
- `Psi_h(alpha, 0) = sum_i alpha_i ell_h(theta_i - q_i) = -J_h(alpha)` is real.
- `d/dphi_j = i z_j d/dz_j`, and `d Psi_h / d z_j` at `theta'` is
  `d Psi_h(alpha; s')/d s_j = 0` by D1(d). So the gradient vanishes.
- `-Hess_phi Psi_h(alpha, 0) = Theta' H_h Theta'`, because the first derivatives vanish.
  This is real symmetric and positive definite by D1(d), and continuous on the
  compact set `P`. So its least eigenvalue is at least some `sigma_min > 0` on `P`.

*Hypothesis (iii), in the localized form.* Choose `eps <= eps_1` with
`(k-1)^3 B_Psi eps <= 3/2 sigma_min`. For `i >= 2`,

    |p_i + h theta_i e^{i phi}|^2 = (p_i + h theta_i)^2 - 2 p_i h theta_i (1 - cos phi),

so `(n_i - 1) log(|p_i + h z_i| / (p_i + h theta_i)) <= -(n_i - 1) p_i h theta_i (1 - cos phi_i) / (p_i + h theta_i)^2`.
With `n_i - 1 >= n_i/2 = T alpha_i/(2h)`, which holds once `n_i >= 2`, i.e.
`N >= N_0(K)`, this is at most `-T c_* (1 - cos phi_i)`, where
`c_* = min_K alpha_i p_min theta_min / (2(1 + h_* theta_max)^2) > 0`. For `i = 1`,
`|p_1 + h g(z')| <= p_1 + h theta_1`. Hence on `{||phi|| >= eps}` the full integrand of
(3.1) has modulus at most

    h^(k-1) b(theta') prod theta_i prod_i (p_i + h theta_i)^(n_i - 1) e^{-c_* (1 - cos eps) T}
      = h^(k-1) e^{T Psi_h(alpha,0)} a_h(alpha,0) e^{-eta T},     eta = c_*(1 - cos eps).

*Laplace.* The proof of `lem:laplace` uses the integrand outside the cube
`{||phi|| <= eps}` only through the localization bound
`|integrand| <= B e^{T(Psi(0) - eta)}`, and inside it uses only `B_Psi`, `B_a` and
`sigma_min` (Remark `rem:laplace-uniform`). So it applies with the bound just
proved, uniformly on `P` and for `T >= 1`, and gives

    int = e^{-T J_h(alpha)} (2 pi/T)^((k-1)/2) det(Theta' H_h Theta')^(-1/2) ( a_h(alpha,0) + O(1/T) ).

Here `a_h(alpha, 0) = b(theta') prod theta_i / prod_i(p_i + h theta_i)` is positive and
continuous on `P`, so the bracket is `a_h(alpha,0)(1 + O(1/T))`. Also
`det(Theta' H_h Theta') = prod_{i>=2} theta_i^2 det H_h`, `T J_h = N I_h`, and
`h^(k-1) T^(-(k-1)/2) = N^-(k-1) T^((k-1)/2)`. Hence

    P_N(n) = N^-(k-1) T^((k-1)/2) e^{-N I_h(n/N)} b(theta') / ((2 pi)^((k-1)/2) prod_i(p_i + h theta_i) sqrt(det H_h)) (1 + O(1/T)),

and the constant is `C_F^(h)(alpha)` by D1(e). The constants depend only on `Q`, `mu`,
`h_*` and `K`. ∎

*Where the old error went.* Nothing in this proof compares `(p + hz)^n` with
`e^{t(z - q)}`. The old `T^2/N` is the difference between `N I_h` and `T J_V`
(part (c)) together with `C^(h)/C_F - 1 = O(h)`.

## 5. Proof of Theorem A_h(b)

This is the proof of `thm:facemax`, with the following changes.

- *Target.* `X(v) = N^-(k-1) T^((k-1)/2) K_F^(h)(v) e^{-T lambda_F^(h)(v)}`, and
  `J^v = J_h - v.alpha - lambda_F^(h)(v) >= 0`, which vanishes only at
  `alpha^{*,h}_F(v)` (Lemma D2).
- *The balls.* The set `A = {alpha^{*,h}_F(v) : h in [0,h_*], v in V}` is compact in
  `Delta_F^o` (D2). By D1(b, d), `J_h` and `log C_F^(h)` are real-analytic in
  `(h, alpha)`, and `Hess J_h` is positive definite. So the constants `rho_0, c_U, C_U,
  C_1, C_3` of the proof of `thm:facemax` can be taken uniform in
  `(h, v) in [0, h_*] x V`.
- *Outside `U(v)`.* `J^v(beta)` is lower semicontinuous and positive on the compact
  set of `(h, v, beta)` with `beta` outside `U(v)^o`. Indeed `J_h(beta)` is a supremum
  over `theta` of functions continuous in `(h, beta)`, and `lambda_F^(h)(v)` is
  continuous. So finitely many `theta_j in V_F` give
  `sum_i beta_i L_h(q_i - theta_{j,i}) - v.beta > lambda_F^(h)(v) + 2 eta`. Corollary U_h
  then gives `P_N(n) e^{h<v,n>} <= C (T/N)^(k-1) e^{-T(lambda_F^(h)(v) + 2 eta)}`. This
  is the same bound as before, without the factor `e^{C T^2/N}`.
- *Inside `U(v)`.* By Theorem A_h(a), with the exact factor `e^{h<v,n>}`, `eq:insideU`
  holds with `|E| <= C_2/T` in place of `C_2(1/T + T^2/N)`. The upper and lower bounds
  follow word for word. For the lower bound, take `n^0` with
  `|n^0_i - N alpha^{*,h}_F(v)_i| < 1`.
- *Bounded `T`.* For `1 <= T <= T_2`, the paper's argument (Lemma `lem:discrete` with
  Theorem `thm:local`) applies as it stands, since `T_2 <= N^{1/3}` for `N >= T_2^3`.
- *The maximizer.* `c_U T |x̂|^2 <= C_3 |x̂| + C_4/T` now holds for all
  `T <= h_* N`. The step at line 320 of sec_secondorder, which needed `T <= N^{1/3}` to
  bound `T^2/N <= 1/T`, is no longer needed. So `|x̂| = O(1/T)`.
- *The case `v = 0`.* Lemma D2 gives `e^{-T lambda_F^(h)} = (1 - h lambda_F)^N` and
  `alpha^{*,h}_F = alpha*_F`.

The singleton is `eq:vertexmax` without its expansion. ∎

**Part (c).** By the envelope theorem applied to (1.1),
`d J_h / dh |_{h=0} = (1/2) sum_i alpha_i (q_i - theta_i)^2`, since
`L_h(y) = y + h y^2/2 + O(h^2)` uniformly for bounded `y`. Joint analyticity gives the
`O(h^2)` remainder uniformly on `K`. Multiplying by `T` gives the first line. The second
line is the Taylor expansion of `-log(1 - x)`, and the third is analyticity of
`C_F^(h)` at `h = 0`. ∎

## 6. What this does to the rest of the paper

**Why `N^{1/3}`.** There were two separate effects:
- In the paper, the local law is proved to `T <= N^{1/2}`, with error `O(1/T + T^2/N)`
  (`lem:discrete`).
- The cube root enters only in `thm:facemax`, in the step that locates the maximizer
  (sec_secondorder line 320, "This is the step that needs the exponent 1/3"), and in
  the choice of one range on which `1/T + T^2/N = O(1/T)`.

Part (c) shows that `T^2/N` is a real second-order term of the continuum exponent,
from `-log(1 - x) = x + x^2/2 + ...`. So the continuum exponent fails at
`T ≍ N^{1/2}`, while the discrete exponent has no threshold at all up to `h_* N`.

**Theorem B (`thm:B`).** Theorem B is unaffected. It lives at `T = tau log N`, where
`T^2/N = O(L^2/N)` is negligible.
- Part (i) is `thm:first`(ii)–(iv) at `T = tau L` and does not change.
- Part (ii) (`thm:crossing`) gains something, which I have checked by hand but not
  written into the paper. Every zero of `D_N` in `[1, h_* N]`, not just in
  `[1, N^{1/3}]`, satisfies `eq:crossing`. By A_h(b), on `[1, h_* N]`,

      D_N(T) = -Delta L + Xi_N(T) + log(K_F^(h)/K_G^(h)) + O(1/T),
      Xi_N(T) = N log((1 - h lambda_F)/(1 - h lambda_G)) + (Delta/2) log T,

  and `Xi_N' = lambda_G/(1 - h lambda_G) - lambda_F/(1 - h lambda_F) + Delta/(2T) >= delta`.
  For a singleton `G`, use the exact vertex formula with `K^(h) = mu_i/(1 - h q_i)`. The
  argument of `thm:crossing`(ii) then places every zero in `[Delta L/(2 delta),
  2 Delta L/delta]`. There `h = O(L/N)`, so `Xi_N(T) = Xi(T) + O(L^2/N)` and
  `K^(h) = K(1 + O(L/N))`, and `eq:crossing` follows with the same `O(1/L)`.
- This also removes one of the hypotheses that O4 (uniqueness of the crossing) has
  to work around.
- Not checked: `thm:window`, the complete-graph section (`sec_complete`, which states
  `T <= N^{1/3}` at line 107), and `thm:first`(ii) for reducible faces. For reducible
  faces, Claim A in `app:first` uses `m = ceil(N/T) > |C|^2`, which needs `h` small.
  The boundary layer section uses the continuum density and is untouched.

**For the paper.** Theorem A could be stated as A_h, with A as Corollary (c). Then:
- `lem:discrete` is no longer needed for the local law;
- `lem:upper` becomes Corollary U_h, shorter and exact;
- the intro sentence "we let `T` range from 1 to `N^{1/3}`" becomes `1 <= T <= epsilon N`.

The extra length is about 3 pages: Lemma T_h (half a page), Lemmas D1–D2 (1.5 pages),
and the proof (1 page, mostly "as in `thm:local`"). That is below the plan's estimate
of 6–8 pages.

## 7. Novelty check (scope: the three named sources and three web searches)

- **Kontoyiannis–Meyn**, *Ann. Appl. Probab.* 13 (2003), read in arXiv
  math/0209200, Section 6.
  - Theorem 6.3: for a geometrically ergodic chain and a strongly non-lattice
    bounded functional, `P_x{S_n >= nc} ~ f̌_a(x) / (a sqrt(2 pi n sigma_a^2)) e^{-n Lambda*(c)}`
    as `n -> inf`.
  - Theorem 6.5 is the lattice form, with `c_n` in a fixed interval
    `(eps, A - eps)`.
  - Both are for one fixed kernel, a scalar functional and tail events, with no rate
    and no uniformity over kernels.
- **Hervé–Ledoux**, *Statist. Probab. Lett.* 83 (2013), abstract (arXiv 1306.5353). This
  is a local CLT (scale `t^{-1/2}`, central region) for densities of the additive part
  of a finite Markov additive process with a fixed driving chain. It is not a large
  deviation result.
- **Miller** (1961). I did not read the full text. The paper's own description is the
  eigenvalue method for sums on a fixed finite chain.
- **Searches** (local large deviations with transitions tending to the identity; the
  Markov binomial with `n`-dependent transitions; rare switching):
  - Gaudron–Trouvé (rare transitions; autocorrelation, not occupation laws);
  - Huang–Mandjes–Spreij (SPA 2016, the opposite regime of fast switching);
  - Hwang, *Ann. Appl. Probab.* 8 (1998), "Large deviations of combinatorial
    distributions II": a local large-deviation theorem by saddle point for
    quasi-power generating functions with a fixed `u(s)` (known to me from the search result and the standard form of the theorem, not reread). As usually stated it does not cover a
    family `u_h` that degenerates as `h -> 0`, or vectors;
  - Dobrushin (1953) and Čekanavičius–Vellaisamy (2010), already cited: `d = 2`, limit
    laws and approximations, not exact large deviations.
- **Conclusion (bounded).** No source found states a local large deviation law that is
  uniform as `P = I + hQ -> I`, nor one for the whole count vector of a killed chain.
  The new content is:
  1. Lemma T_h, which puts Good's discrete formula on the same torus as the continuum;
  2. the observation that in the `z` variable the problem is analytic at `h = 0`, so
     that one compact parameter set covers `[0, h_*]`;
  3. the explicit constant `C_F^(h)`.

  It would be fair to call Theorem A_h "Miller's local large deviations, uniform as the
  chain degenerates to the identity, joined to the continuum limit".

## 8. Numerics

Two-state chain `q12 = 1`, `q21 = 2`, `N = 4000`, `alpha = n_1/N`. Commands, run from
this folder (times on this machine):

    py -I o2_smoke.py          # D1(e): the two constants agree; J_0 closed form (2 s)
    py -I o2_exact_checks.py   # P1 (13 s)
    py -I o2_table.py          # P2-P4 (25 s)
    py -I o2_faces.py          # P5-P6 (50 s)

The outputs are in `out_smoke.txt`, `out_exact_checks.txt`, `out_table.txt` and
`out_faces.txt`.

**P1 (exactness): confirmed.**
- The recursion and Good's run sum match brute force for `N <= 14` to `3e-14` in the
  log.
- The recursion and Good's run sum agree at `N = 4000` to `6e-11` (`T = 400`).
- The log of the total mass is `1e-12`.
- On three states, the recursion matches brute force to `9e-15`.

**P2 (plan's table): confirmed exactly, with the uniform start, on the plan's 9-point
grid `alpha = 0.45, 0.50, ..., 0.85`.** On all 1601 lattice points the `T J_V` column
is slightly larger (2.373 and 10.192), because a finer grid reaches the extremes of a
curved function. My prediction of "within 0.01 on all points" was therefore wrong for
that column at `T >= 200`. The cause is the grid, not the law.

| T | T²/N | T J_V (9 pts) | N I_h (9 pts) | T J_V (all) | N I_h (all) | spread log C^(h) |
|---|---|---|---|---|---|---|
| 16 | 0.06 | 0.336 | 0.340 | 0.336 | 0.340 | 0.345 |
| 63 | 0.99 | 0.341 | 0.341 | 0.341 | 0.341 | 0.342 |
| 200 | 10 | 2.344 | 0.333 | 2.373 | 0.333 | 0.333 |
| 400 | 40 | 10.116 | 0.315 | 10.192 | 0.316 | 0.316 |
| 1000 | 250 | 87.883 | 0.218 | 88.447 | 0.219 | 0.219 |

New reading of the plan's table: the residual spread is not a fixed prefactor of
about 0.33. It is the spread of `log C_F^(h)`, which itself moves with `h`
(0.345 at `h = 0.004`, 0.219 at `h = 0.25`). The last column matches the `N I_h`
column to within the `O(1/T)` error.

**P3 (the constant and the full local law): confirmed.**
- The Hessian and torus forms of `C^(h)` agree to `1e-9` to `5e-9`, for `k = 2` and
  `k = 3`, `h` up to 0.25, where finite differences limit the agreement.
- `R = P_N(n) / (N^-1 T^(1/2) C^(h) e^{-N I_h})` has `max T |R - 1| <= 0.16`
  (uniform start) and `<= 0.20` (stationary start) for every `T` in
  `{16, 63, 200, 400, 1000}`.
- With the continuum `T J_V` and `C_F`, `T |R - 1|` is 0.33, 11.7, 180, 400 and 1000.

`T (R - 1)` at `alpha = 0.45, 0.55, 2/3, 0.75, 0.85`:

    T=   16: -0.0842  -0.0841  -0.0939  -0.1111  -0.1590
    T=   63: -0.0821  -0.0820  -0.0913  -0.1078  -0.1539
    T=  200: -0.0778  -0.0773  -0.0857  -0.1011  -0.1444
    T=  400: -0.0725  -0.0715  -0.0789  -0.0930  -0.1338
    T= 1000: -0.0691  -0.0667  -0.0738  -0.0896  -0.1408

The `1/T` coefficient is stable across a factor 60 in `T` and a factor 60 in `h`,
which is what uniformity in `h` predicts.

**P4 (the `T^2/N` term): confirmed.** The ratio `(N I_h - T J_V) / [(T^2/2N) sum alpha_i (q_i - theta_i)^2]`
at `alpha = 0.45, 0.55, 0.85` is 1.006 at `h = 0.004`, 1.025 at `h = 0.016` and 1.08 at
`h = 0.05`, so it tends to 1 linearly in `h`. It is 1.18 at `h = 0.1`, slightly above
my predicted 15%.

**P5 (a proper face with an exit rate): confirmed.**
- Setup: three states, `A = [[0,2,0.7],[0.5,0,1],[1.5,0.3,0]]`, conservative,
  `mu = (0.5, 0.3, 0.2)`, face `{1,2}` with `lambda_F = 0.93381` and
  `alpha*_F = (0.2428, 0.7572)`, `N = 4000`.
- `M_F / new` is 0.99952, 0.99976, 0.99984, 0.99989, 0.99994, 0.99996, 0.99995 for
  `T = 16, 40, 63, 100, 200, 400, 1000`.
- `M_F / old`, with `K_F e^{-T lambda_F}`, is 0.980, 0.856, 0.667, 0.348, 0.012, 0 and 0.
  It tracks `exp(-T^2 lambda_F^2/2N)`.
- `T |n̂/N - alpha*_F| <= 0.17`.
- The minimum of `J_h` is at `alpha*_F` with value `-log(1 - h lambda_F)/h` to 10 digits,
  for every `h`.

**P6 (`k = 3`, non-reversible).**
- Setup: the same chain on its full face. Its cycle products are 3 and 0.105.
  `N = 600`, `T = 20, 40, 60`, four interior points.
- `R` is 0.986–0.989 at `T = 20`, 0.993–0.995 at `T = 40` and 0.996–0.997 at
  `T = 60`. `T (R - 1)` lies between −0.20 and −0.28 and is stable.
- With the continuum exponent, `R` ranges from 0.50 to 1.19 at `T = 60`.

## 9. Paper labels used

`thm:A`, `thm:B`, `thm:local`, `thm:stratified`, `thm:facemax`, `thm:crossing`,
`thm:first`, `thm:window`, `lem:runs`, `lem:continuum`, `lem:discrete`, `lem:upper`,
`lem:torus`, `lem:torus-complex`, `lem:local-general`, `lem:laplace`,
`rem:laplace-uniform`, `lem:perron`, `lem:face-monotone`, `prop:restriction`,
`prop:rate`, `prop:variational`, `prop:constant`, `def:tilt`, `eq:A-radii`, `eq:A-fT`,
`eq:stationary`, `eq:vertexmax`, `eq:logmax`, `eq:insideU`, `eq:crossing`,
`app:first`, `sec:locallaw`.

## 10. Honest status and what to check

- **Complete:** Lemma T_h, Corollary U_h, Lemma D1(c)–(e) (algebra confirmed
  numerically to `1e-9`), and the Laplace step of section 4.
- **Routine but not written out line by line:**
  1. The localized form of `lem:laplace`. Its proof uses the integrand outside the
     cube only through the modulus bound. This is clear from the text of the proof,
     but the paper's statement assumes `Psi` is defined on the whole torus.
  2. The uniform constants in section 5. They follow from joint real-analyticity on
     `[0, h_*] x Delta_F^o` and compactness of `A`. I did not re-derive each of
     `rho_0, c_U, C_U, C_1, C_3`.
  3. Lemma D2's boundary claim on reducible subfaces, by the same Perron argument as
     `lem:face-monotone`.
- **Hypothesis to keep:** `h_* q_max < 1`. Strict concavity in D1(b) uses `p_i > 0`.
  At `h q_i = 1` the chain may become periodic, and then the local law can fail.
  The paper's standing `hq_max <= 1/2` is inside this range.
- **Not done:** reducible faces (`thm:first`(ii)) for `T` beyond `N^{1/3}`, the tie
  windows, and the complete-graph statements beyond `N^{1/3}`.
- **No missing lemma** in the main line of A_h(a) or (b).
