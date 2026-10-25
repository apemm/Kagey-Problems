# Paper C1, item O2: audit of Theorem A_h

25 October 2026. Audit of `01_report.md` in this folder against Paper C1
(`kagey-problems/problem131/paperC`, working tree, read only). Sources read: `sec_model.tex`
(Lemmas `lem:runs`, `lem:continuum`), `sec_firstorder.tex` (Lemma `lem:upper`),
`sec_secondorder.tex` (Theorems `thm:local`, `thm:facemax`, `thm:crossing`, the maximizer step),
`app_torus.tex`, `app_laplace.tex`, `sec_intro.tex` (Theorem B). I judged only the mathematics
and ignored the report's own status language.

**Verdict: proved as written, apart from three small repairs that leave the theorem unchanged
(section 6). None of them is a missing implication.**

## 1. Claim card

- *Hypotheses.* `Q`, `mu` fixed. `F` satisfies (H) with `k >= 2`. `K` is a compact subset of
  `Delta_F^o`. `h_*` is fixed with `h_* q_max < 1`, so `p_i = 1 - h q_i >= p_min = 1 - h_* q_max > 0`
  for `h <= h_*`.
- *Rate.* `J_h(alpha) = sup_{theta in V_F} sum_i alpha_i L_h(q_i - theta_i)`, with
  `L_h(y) = -log(1 - h y)/h` and `J_0 = J_F`. For `h > 0`, `h J_h = I_h`, the discrete
  Donsker-Varadhan rate of `I + hQ`, and `T J_h = N I_h`.
- *Constant.* With `theta = theta^h(alpha)` the maximizer, `r, l` the null vectors of
  `A_F - diag theta` and `c_h = sum_i alpha_i/(p_i + h theta_i)`:
  `C_F^(h) = c_h (mu.r)(l.1) sqrt(det Hess J_h / (2 pi)^(k-1))
  = b(theta') / ((2 pi)^((k-1)/2) prod_i (p_i + h theta_i) sqrt(det H_h))`,
  `H_h` the Hessian in `s'` of `Psi_h(alpha; s') = sum_i alpha_i ell_h(s_i - q_i)`, `s_1 = g(s')`,
  `ell_h(x) = log(1 + hx)/h`. `K_F^(h)(v) = C_F^(h)(alpha^{*,h}_F(v))`.
- *(a)* For `N >= N_0`, `1 <= T <= h_* N`, `supp n = F`, `n/N in K`:
  `P_N(n) = N^-(k-1) T^((k-1)/2) C_F^(h)(n/N) e^{-N I_h(n/N)} (1 + O(1/T))`.
- *(b)* For `v` in a compact `V`, on the same range,
  `M_F(T,v) = N^-(k-1) T^((k-1)/2) K_F^(h)(v) e^{-T lambda_F^(h)(v)} (1 + O(1/T))`, every maximizer
  within `O(1/T)` of `alpha^{*,h}_F(v)`; at `v = 0`, `e^{-T lambda_F^(h)} = (1 - h lambda_F)^N` and
  `alpha^{*,h}_F = alpha*_F` for all `h`.
- *(c)* Expansions in `h` that recover Theorem A for `T <= N^{1/2}`.

## 2. The critical step, derived independently

*Torus form.* The coefficient of `z^{m-1}` in `(p + hz)^{n-1}` is `h^{m-1} C(n-1, m-1) p^{n-m}`,
and it is `0` for `m > n` because the polynomial has degree `n - 1`. So
`(1/2pi) int (p + hz)^{n-1} z^{1-m} dphi` is this coefficient for `m >= 1` and `0` for `m <= 0`.
Term-by-term integration of the word series of `mu^T (Z - A_F)^{-1} 1` (absolutely and uniformly
convergent on the torus by Step 3 of `lem:torus`, which does not involve `t` or `h`) gives
`h^{-(k-1)}` times the run sum of `lem:runs`. In the first circle, `z_1` cancels the measure
`dphi_1 = dz_1/(i z_1)`. The term `mu'^T X 1` gives `int poly(z_1) z_1 dphi_1 = 0`, and the term
`b/(z_1 - g)` gives the polynomial at `z_1 = g(z')`, since `|g(z')| <= g(s') < s_1`. This is (3.1)
of the report, with no condition on `h` beyond `p_i >= 0`. Confirmed.

*Exponent and amplitude.* `n_i = T alpha_i / h` exactly because `alpha = n/N`. So
`prod (p_i + h z_i)^{n_i - 1} = e^{T Psi_h} / prod (p_i + h z_i)` wherever a logarithm is chosen,
with `Psi_h = sum alpha_i ell_h(z_i - q_i)`. At the real point,
`T Psi_h(alpha, 0) = sum n_i log(p_i + h theta_i) = -T J_h(alpha)`, because `L_h(y) = -ell_h(-y)`.

*Analyticity at h = 0.* `ell_h(x) = int_0^1 x ds/(1 + s h x)`. Since
`1 + s h x = (1 - s) + s (1 + h x)`, it is analytic in `(h, x)` wherever `Re(1 + h x) > 0`,
including `h = 0` and small negative `h`, and `ell_0(x) = x`. On the torus of radii `theta'` with
`|phi_i| <= pi/2`, `Re(p_i + h z_i) >= p_i >= p_min`. For state `1`, `g(z')` is within a uniform
distance of `theta_1 > 0` on a small cube by uniform continuity. So `Psi_h` and `a_h` are
real-analytic in `(h, alpha, phi)` on `[0, h_*] x K x {||phi|| <= eps_1}`. At `h = 0` they are
`(Psi - <q, alpha>, chi)` of `eq:A-fT`. Confirmed.

*Laplace hypotheses, uniformly on P = [0, h_*] x K.*
- (i) The gradient in `phi` is `i z_j d Psi/d z_j`, which vanishes at `theta'` because `theta'`
  is a critical point of the real function `Psi_h(alpha; .)` (Lemma D1(d), checked in section 3).
- (ii) With first derivatives zero, `d^2/dphi_i dphi_j = -theta_i theta_j d^2/dz_i dz_j`, so
  `-Hess_phi = Theta' H_h Theta'`, real symmetric, positive definite, and continuous on the
  compact `P`. Hence `sigma_min > 0`.
- (iii) `|p + h theta e^{i phi}|^2 = (p + h theta)^2 - 2 p h theta (1 - cos phi)` (checked), so
  for `i >= 2` the factor `|p_i + h z_i|^{n_i - 1}` loses at least
  `exp(-T alpha_i p_i theta_i (1 - cos phi_i) / (2 (p_i + h theta_i)^2))` once `n_i >= 2`, and
  `|p_1 + h g(z')| <= p_1 + h theta_1`. With `p_i >= p_min`, `theta_i >= theta_min`,
  `p_i + h theta_i <= 1 + h_* theta_max`, this gives a gap `eta = c_* (1 - cos eps)` uniform on
  `P`, including `h -> 0`, since the `h` in `n_i = T alpha_i / h` cancels the `h` in
  `p h theta`.

*Role of h_* < 1/q_max.* (1) `I + hQ >= 0` and `p_i > 0`. (2) `|p_i + h z_i| < p_i + h theta_i`
off `phi_i = 0` needs `p_i > 0`. (3) Strict concavity of `G_h` in D1(b) needs the weight `p_i > 0`
on the value `0`; with `p_i = 0` the variance can vanish for `delta` with `delta_j - delta_i`
equal to a nonzero constant along the edges out of `i`, which is the periodic case. (4) The base
need not be nonvanishing on the whole torus. Zeros of `p_i + h z_i` occur only on the circle of
radius `p_i/h`, and the proof uses the integrand away from the cube only through its modulus. On
the cube the base has real part at least `p_min/2`. So the condition the report needs is (1)-(3),
and all hold for `h <= h_*`.

## 3. The routine checks, written out

**3.1. The localized Laplace lemma.** The paper's `lem:laplace` and `rem:laplace-uniform` assume
`Psi` is smooth on the whole torus, which fails here because `log(p_i + h z_i)` has no global
branch when `theta_i > p_i/h`. The proof of `lem:laplace` uses the integrand at
`||phi|| >= eps` only in the localization paragraph, through
`|integrand| <= B_a e^{T(Psi(0) - eta)}`, and uses `B_Psi`, `B_a` only on the cube
`||phi|| <= eps` (Taylor with integral remainder, the bound `|R| <= sigma_min |phi|^2 / 4`, and
the expansion of `a`). Here the bound outside the cube is
`h^{k-1} e^{T Psi_h(alpha,0)} a_h(alpha,0) e^{-eta T}` (checked: `e^{T Psi_h(0)} a_h(0)` equals
`b(theta') prod theta_i prod (p_i + h theta_i)^{n_i - 1}`), with `a_h(alpha,0)` bounded on `P`,
and `(2 pi)^{k-1} e^{-eta T} <= C T^{-1-(k-1)/2}`. The choice `eps <= eps_1` with
`(k-1)^3 B_Psi eps <= 3 sigma_min / 2`, `B_Psi` taken on the cube, is consistent. So the
expansion holds uniformly on `P` for `T >= 1`. The paper should state this as a sentence in
`rem:laplace-uniform` ("the bounds are needed only on the cube, and outside it only a modulus
bound"), not leave it implicit. **Holds.**

**3.2. Lemma D1.**
- (a) For `j` not in `F`, lowering `u_j` lowers `(Pu)_i` and does not change the terms with
  `alpha_i > 0`; as `u_j -> 0`, `P` becomes `P_F` with diagonal `1 - h q_i`, which keeps the full
  exit rate. **Holds.**
- (b) `-G_h = (1/h) sum alpha_i log(p_i + sum_j h q_ij e^{psi_j - psi_i})` (checked from
  `1 - h(q_i - theta_i) = p_i + h theta_i`). The variance argument is right and needs `p_i > 0`
  and `alpha_i > 0`. Coercivity: with `psi_1 = 0`, the spread `max psi - min psi -> infinity`, a
  path in the strongly connected `G_F` gives an edge with increment at least spread`/(k-1)`, and
  `L_h(q_i - theta_i) -> -infinity` as `theta_i -> infinity` (logarithmically for `h > 0`,
  enough for existence at each `(h, alpha)`). The other terms are at most `q_max/p_min`. The
  maximizer is the unique critical point, so the implicit-function branch through it is the
  maximizer, which gives analyticity in `(h, alpha)` including `h = 0` (`G` is analytic for small
  negative `h` near the maximizer). **Holds.**
- (c) `dL_h/dy = 1/(1 - h y) = 1/(p_i + h theta_i)`. The continuum criterion: `w_i/u_i` is a left
  null vector of `A_F - diag theta`, hence proportional to `l_i`. **Holds.**
- (d) `psi -> theta(psi)'` is a bijection of `{psi_1 = 0}` onto `Omega` with analytic inverse
  (`theta_1 = g(theta')` by `eq:A-radii`; conversely `(1, X(s') b_1)` is a nonnegative and hence
  positive Perron vector). `G_h(alpha, psi) = -Psi_h(alpha; theta(psi)')` (checked). At the
  critical point the Hessians are congruent through the invertible Jacobian. The Hessian of
  `J_h`: envelope `dJ_h/d alpha_j = -(y_j - y_1)`, then `d s'/d alpha' = -H_h^{-1} K`, so
  `Hess J_h = K^T H_h^{-1} K`. `K_ij = delta_ij e_j + e_1 pi_i/pi_1` with
  `g_i = -pi_i/pi_1`, and the matrix determinant lemma gives
  `det K = prod_i e_i * sum_i pi_i/e_i / pi_1 = 1/(c_h pi_1 prod_i (p_i + h theta_i))`, using
  `alpha_i = c_h pi_i (p_i + h theta_i)`. All checked by hand. **Holds.**
- (e) `b(theta') = (mu.r)(l.1)/pi_1` from `lem:local-general` at the point `pi`, and
  `det Hess J_h = det K^2 / det H_h`. Combined: both forms of `C_F^(h)` agree. At `h = 0`,
  `det H_0 = det Sigma_alpha / alpha_1^2` and the torus form reduces to
  `(2 pi)^{-(k-1)/2} alpha_1 b(theta') / sqrt(det Sigma_alpha) = C_F`. **Holds.**
- The final assembly `h^{k-1} (2pi)^{-(k-1)} (2pi/T)^{(k-1)/2} det(Theta' H Theta')^{-1/2} a_h(0)
  = N^{-(k-1)} T^{(k-1)/2} b / ((2pi)^{(k-1)/2} prod(p_i + h theta_i) sqrt det H_h)` is right.

**3.3. Lemma D2.** `J_h - v.alpha = (1/h) sup_u sum alpha_i log(u_i/(Mu)_i)` with
`M = e^{h diag v} P_F`. With `u = (s - M)^{-1} 1`, `Mu = su - 1 < su`, and `Mu > 0` because `M`
has positive diagonal, so every ratio exceeds `1/s`; this works for every `alpha in Delta_F`,
boundary included. `u = r(M)` gives equality exactly at `alpha = l o r` of `M`. Interior
uniqueness from `Hess J_h > 0`. At `v = 0`, `rho(I + h Q_F) = 1 - h lambda_F > 0` with the
Perron vectors of `Q_F`. `-(1/h) log rho(M)` is analytic at `h = 0` because `rho(M)` is a simple
eigenvalue, analytic, equal to `1` at `h = 0`. **Holds.**

Boundary claim (report item 3). For `beta in Delta_{F'}`, `F'` a proper subface (possibly
reducible), one needs `J_h^F(beta) - v.beta >= lambda_{F'}^(h)(v)`. The direct comparison goes
the wrong way (`(P_F u)_i >= (P_{F'} u)_i` gives `J^F <= J^{F'}`). The correct step is the
argument of D1(a) one level down: letting `u_j -> 0` for `j in F \ F'` shows
`J_h^F(beta) >= J_h^{F'}(beta)`, so the two are equal on `Delta_{F'}`. Then the resolvent lower
bound for the principal submatrix `M_{F'}` (positive diagonal, any graph) gives
`>= -(1/h) log rho(M_{F'})`, and `rho(M_{F'}) < rho(M)` because `M` is irreducible and
nonnegative and `M_{F'}` is a proper principal submatrix. **Holds**, with "by D1(a)" read as
"by the argument of D1(a) applied to `F' subset F`".

**3.4. Uniform constants in section 5.** `A = {alpha^{*,h}_F(v)}` is the continuous image of the
compact `[0, h_*] x V`, hence compact in `Delta_F^o`. `J_h`, `log C_F^(h)` are jointly analytic on
`[0, h_*] x Delta_F^o` and `Hess J_h = K^T H_h^{-1} K` is positive definite and continuous, so a
single `rho_0` and single `c_U, C_U, C_1, C_3` serve for all `(h, v)`: the eigenvalues of
`Hess J_h` are bounded above and below on the compact `rho_0`-neighborhood of `A` (times
`[0, h_*]`), and third derivatives are bounded there. Outside `U(v)`: for fixed `theta in V_F`,
`(h, beta) -> sum beta_i L_h(q_i - theta_i)` is continuous on `[0, h_*] x Delta_F` (since
`q_i - theta_i <= q_i` keeps `1 - h(q_i - theta_i) >= p_min`), so `J^v` is lower semicontinuous
in `(h, v, beta)`, positive on the compact set where `beta` is outside `U(v)^o` (interior by D2
uniqueness, boundary by 3.3), hence at least `3 eta`. Finitely many `theta_j` follow from
continuity of `lambda_F^(h)(v)`. Corollary U_h then gives
`P_N(n) e^{h<v,n>} <= C h^{k-1} e^{-T(lambda_F^(h)(v) + 2 eta)}`, using
`prod_i (p_i + h theta_i)^{n_i} = e^{-T sum beta_i L_h(q_i - theta_i)}` and
`prod (p_i + h theta_i)^{-1} <= p_min^{-k}`. **Holds.**

## 4. The specific claims

**Lemma upper without `e^{CT^2/N}`.** Corollary U_h is the modulus bound of (3.1) on the torus of
radii `theta'`, valid for `h q_max <= 1`, any length `|n|`, any `theta in V_F`. Since
`-log(1 - x) >= x`, `L_h(y) >= y`, so
`prod (p_i + h theta_i)^{n_i} <= e^{-h<n, q - theta>}`. Hence U_h implies `lem:upper` in its
original form with the `C_theta h^2 |n|` term deleted, for `h q_max <= 1/2`, with
`C_theta = p_min^{-k} b(theta') prod theta_i`. The report states the weaker reading; the stronger
one is also true. **Confirmed.**

**Maximizers within `O(1/T)` of `alpha*_F` for every h.** With A_h(a), `eq:insideU` holds with
`|E| <= C_2/T`, so the comparison with `n^0` gives `c_U T |x|^2 <= C_3 |x| + C_4/T` for all
`T_3 <= T <= h_* N`, with constants uniform in `h` by 3.4; `T J^v(n^0/N) <= C_U k^2 T/N^2 = O(1/N)`
on the whole range. The step that needed `T^2/N <= 1/T` is gone. At `v = 0`,
`alpha^{*,h}_F = alpha*_F` because `I + hQ_F` and `Q_F` share Perron vectors. For bounded `T`, the
paper's argument still applies, because `X^(h)/X^(0) = 1 + O(T_2^2/N)` there. **Confirmed.**

**Theorem B and the crossing equation on `[1, h_* N]`.** From A_h(b) at `v = 0` and the exact
singleton formula `M_{j} = (mu_j/(1 - h q_j)) (1 - h q_j)^N`,
`D_N = -Delta L + Xi_N(T) + log(K_F^(h)/K_G^(h)) + O(1/T)` on `[1, h_* N]`, with
`Xi_N = N log((1 - h lambda_F)/(1 - h lambda_G)) + (Delta/2) log T`. Since `x -> x/(1 - hx)` is
increasing and convex on `[0, 1/h)` and `lambda_G <= q_max < 1/h`,
`Xi_N' >= delta/(1 - h lambda_F)^2 >= delta`. `log(K_F^(h)/K_G^(h))` is bounded on `[0, h_*]` by
continuity and positivity. So for a zero, `Xi_N(T_N) = Delta L + O(1)`; `Xi_N(T) >= delta T` for
`T >= 1` gives `T_N <= 2 Delta L/delta + O(1)`, and `Xi_N(Delta L/(2 delta)) = Delta L/2 + O(log L)`
gives the lower end. In that window `h = O(L/N)`, `Xi_N = Xi + O(L^2/N)`,
`K^(h) = K (1 + O(L/N))`, and `eq:crossing` follows with `O(1/L)`. **Confirmed.**

The report undersells one point. Since every zero in `[1, h_* N]` lies in
`W = [Delta L/(2 delta), 2 Delta L/delta]`, which is inside `[1, N^{1/3}]`, part (iv) of
`thm:crossing` (strict increase on `W`, via `lem:derivative`) applies unchanged. So Theorem B(ii)
holds with "exactly one root in `[1, h_* N]`", not only "every root satisfies the equation".
Theorem B(i) lives at `T = tau L` and is unaffected.

**Part (c).** The envelope theorem with `d L_h/dh |_{h=0} = y^2/2` and joint analyticity give the
first line; the other two lines are clear. The claim that (a), (b) give back Theorem A for
`T <= N^{1/2}` is right. One sentence is wrong: the exception "except where
`alpha -> sum alpha_i (q_i - theta_i)^2` is constant on `K`" does not make the `T^2/N` term
removable from the pointwise local law. A constant `c T^2/(2N)` is still an error of that size
unless `c = 0`, and `c = 0` forces `theta = q`, which happens only at one point and only when
`lambda_F = 0`. The exception applies to spreads across `K`, not to the law. Similarly, for the
maxima with `lambda_F = 0`, `K_F^(h) = K_F (1 + O(h))` still carries an `O(T/N)` term. This is a
remark, not part of the theorem.

## 5. Numeric spot check (own code)

Script `check.py` in my scratch folder, run with `py -I`, 40-digit `mpmath`. Two-state chain
`q12 = 1`, `q21 = 2`, uniform start, `N = 4000`. Exact `P_N(n)` from the run sum of `lem:runs`
(not the report's recursion). Approximation from my own saddle point of the two-state integral
`h/(2pi) int (p_1 + h q12 q21/z)^{n_1 - 1} (p_2 + hz)^{n_2 - 1} b(z) z dphi`, with the saddle
from the closed-form quadratic `alpha_2 p_1 s^2 + (alpha_2 - alpha_1) h q12 q21 s - alpha_1 q12 q21 p_2 = 0`.

`T (R - 1)` at `alpha = 0.45, 0.55, 2/3, 0.75, 0.85`:

    T=  16  -0.0842 -0.0841 -0.0939 -0.1111 -0.1590
    T=  63  -0.0821 -0.0820 -0.0913 -0.1078 -0.1539
    T= 200  -0.0778 -0.0773 -0.0857 -0.1011 -0.1444
    T= 400  -0.0725 -0.0715 -0.0789 -0.0930 -0.1338
    T=1000  -0.0691 -0.0667 -0.0738 -0.0896 -0.1408   (h = 0.25, h q_max = 0.5)
    T=1600  -0.1234 -0.1394 -0.1633 -0.1859 -0.2547   (h = 0.40, h q_max = 0.8)

The first five rows agree with the report's table to all four digits, so its constant and mine
coincide. The claim `T |R - 1| <= 0.2` up to `T = N/4` holds (max 0.159). Beyond the report's
range, at `h q_max = 0.8`, `T |R - 1|` stays bounded (0.255), as the theorem predicts with a
constant that depends on `h_*`.

## 6. Repairs (none changes the statement)

1. State the localized Laplace lemma (3.1 above) as a sentence in `rem:laplace-uniform`: bounds on
   the derivatives are needed only on the cube `||phi|| <= eps`, and outside it a modulus bound
   `|integrand| <= B e^{T(Re Psi(0) - eta)}` suffices. Lemma `lem:laplace` as stated does not
   cover (3.1), because `log(p_i + h z_i)` has no branch on the whole torus.
2. In Lemma D2, cite "the argument of D1(a) for `F' subset F`" to get `J_h^F = J_h^{F'}` on
   `Delta_{F'}` before the subface lower bound; the comparison of `P_F` with `P_{F'}` alone goes
   the wrong way.
3. Drop or rephrase the two exceptions in part (c) (section 4).

Optional strengthenings the report missed: U_h implies `lem:upper` with no `h^2 |n|` term in its
original exponent; Theorem B(ii) gets "exactly one root in `[1, h_* N]`".

Not audited, as the report also leaves them: reducible faces (`thm:first`(ii)) beyond `N^{1/3}`,
`thm:window`, the complete-graph section, the novelty paragraph.
