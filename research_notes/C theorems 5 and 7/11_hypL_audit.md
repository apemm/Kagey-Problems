# Audit of the spectral route to Hypothesis L

Date October 24, 2026. Read-only on the paper and on note 10. Files written: this note,
`11_hypL_audit_check.py`, `11_hypL_audit_output.txt`,
`11_rerun_of_10_output.txt`.

Sources. The statement audited is `hyp:L` at line 366 of `kagey-problems/problem131/paperC/sec_boundary.tex`
as committed this morning (commit `12e9db8`, 15:14). The folder `paperC2` does not contain
`sec_boundary.tex`, so the committed file was used. The working copy of `sec_boundary.tex` has since
renamed the hypothesis: it is now the conclusion of `lem:L-two` restated in `rem:layer-four` for
`|G| >= 3`, with the same quantifiers, the same error `|eps| <= C/S` and the same normalizing constant.
Nothing below depends on which name is used. Also read: `sec_model.tex` (`lem:continuum`, (H)),
`sec_dv.tex` (`prop:rate`, `eq:Jfield`), `sec_secondorder.tex` (`def:tilt`, `prop:constant`),
`app_torus.tex` (`lem:perron`, `lem:torus`, the proof of `thm:local`), `app_laplace.tex`
(`lem:laplace`, `rem:laplace-uniform`), and the note `10_hypL_spectral_route.md` with its script and
output.

## 1. The claim

Let `G` satisfy (H): `G` irreducible and `mu(G) > 0`. Let `g = |G| = k - 1 >= 2`, let `i` be a state
outside `G` with `F = G + {i}` irreducible, and let `K` be a compact subset of the open simplex on
`G`. Put `c^-_j = q_{ji}`, `c^+_j = q_{ij}`, and for complex `z`

    A(z) = A_G + z offdiag(c^- (c^+)^T),   d(z) = q_G - z c^- o c^+,
    mu^(z) = mu_G + z mu_i c^+,            e^(z) = 1 + z c^-,

    f^(z)_G(s) = e^{-<d(z),s>} sum_{m in Z_{>=1}^G} W_z(m) prod_j s_j^{m_j-1}/(m_j-1)!,
    W_z(m) = sum over words w in G with no two equal neighbours and m_j letters j of
             mu^(z)_{w_1} prod_l A(z)_{w_l w_{l+1}} e^(z)_{w_last}.

Claim. There are `z_0 > 0`, `C`, and functions `J_G(beta,z)`, `C_G(beta,z)` on
`K x {|z| < 2 z_0}` that are holomorphic in `z`, jointly continuous, real for real `z`, equal for
real `0 <= z < 2 z_0` to the rate of `Q_G(z) = A(z) - diag d(z)` (the supremum `eq:Jfield` with
`Q_G(z)` in place of `Q_F`) and to the constant

    (mu^(z) . r_beta(z)) (l_beta(z) . e^(z)) / ((2 pi)^{(g-1)/2} sqrt(det Sigma_beta(z)))

of `def:tilt` for `A(z)`, with `C_G(beta,0) = C_G(beta) > 0`, such that for all `beta` in `K`,
all `S >= 1` and all complex `|z| <= z_0`

    f^(z)_G(S beta) = S^{-(g-1)/2} C_G(beta,z) e^{-S J_G(beta,z)} (1 + eps),   |eps| <= C/S,

with `C` independent of `beta`, `S`, `z`.

By `lem:continuum`, `f^(0)_G = f_G` is the density of the occupation times of the continuous-time
chain with generator `Q` on the event that it stays in `G` and visits every state of `G`. The
object is a word series. No time parametrization is part of the statement.

## 2. Verdict

Proved as written. The note's proof establishes `hyp:L` for every `g >= 2` with the functions of its
Theorem L. One constant is chosen wrongly in Step 6: `z_0 = min(z_1, z_2/2)` must be
`z_0 = min(z_1, z_3/2)`. Step 7 needs the eigenvalue `nu` and the bound `Re H_Phi >= sigma_0/2`
on the whole disc `|z| < 2 z_0`, and Step 1 provides them only for `|z| <= z_3`. Since
`z_1 <= z_3 <= z_2`, the corrected choice is smaller and every other step is unchanged. This is a
slip in bookkeeping, not a gap in the argument.

## 3. Dependency graph

    hyp:L  <=  Theorem L (Steps 1 to 7)
      Step 2 split            <=  Lemma R (exact torus formula)  <=  algebra, absolute convergence
                               <=  Lemma T (complex tilt)        <=  lem:perron (Sigma_beta > 0), holomorphic IFT
                               <=  Lemma D (Doob transform)      <=  algebra
      Step 3 (I_2)            <=  (S3) Perron gap at z = 0, Riesz projection, continuity
      Step 4 (I_3)            <=  (S1) norm bound, (S2) |u(psi)| <= 1 - c_eps, continuity in z
      Step 5 (I_1)            <=  Lemma CL (complex Hessian Laplace)  <=  (S4) Re H_Phi >= sigma_0 at z = 0
      Step 6 assembly         <=  a(0) bounded below  <=  (H): mu(G) > 0
      Step 7 identification   <=  Lemma H (determinant identity)  <=  proof of thm:local, paragraphs (i),(ii), for A(z), real z >= 0
                               <=  prop:rate(b) criterion, def:tilt  (J_G = <d - theta, beta>)

Leaves: internal algebra (R, D, H), the paper's `lem:perron`, `prop:rate`, `def:tilt`, `lem:torus`
and the proof of `thm:local` (all stated for irreducible Metzler matrices, which `Q_G(z)` is for
real `z >= 0`), the holomorphic implicit function theorem, the Riesz functional calculus, and
the identity theorem in several variables. No external source beyond standard analysis. No
circularity: Lemma R does not use `lem:torus`, and Lemma H is used only for the identification of
the constant for real `z`, after the estimate is proved.

## 4. Obligation matrix

| # | Obligation | Status | Evidence |
|---|---|---|---|
| 1 | Same object as `hyp:L` | passed | Lemma R is an identity for the word series `f^(z)_G(s)` itself. The expansion of `exp(c_psi K_psi)` is the algebraic series, not a time discretization. The paper's chain is in continuous time (`lem:continuum`); the discrete chain `I + hQ` enters only `lem:discrete` and `lem:layer-exact-discrete`, which `hyp:L` does not involve. The factor `e^{c_psi(s)}` is the Cauchy transform of `s^{m-1}/(m-1)!`, that is, of the exponential holding times. Same normalization `S^{-(g-1)/2}`, same `C_G`, same `J_G`. No change of parametrization anywhere. |
| 2 | Lemma R, exactness and absolute convergence for complex radii | passed | Rederived (Section 5.1). The triple series is dominated by `sum_n (sum_j s_j |theta_j|)^n / n!` times a geometric factor, for every `theta` in `(C \ 0)^g` and every `z`, uniformly in `psi`. Term by term integration keeps exactly `k_j = m_j - 1`, and the powers of `theta_j` cancel. Numerically: relative agreement `1e-16` to `1e-15` with the word series on the two new facets, real and complex radii, `z = 0` and `z = 0.3 - 0.4i`. |
| 3 | (S2) non-lattice bound, periodic jump chains | passed | `|u|^2 = 1 - sum_{j,k} w_j w_k (1 - cos(psi_j - psi_k))` with `w > 0`, `sum w = 1` at `z = 0`; the pair `(1,k)` gives the bound; `w_min` is a positive minimum over compact `K`. The spectrum of `P_psi` never enters away from `psi = 0`: Step 4 uses only `||P_psi|| = ||P_0||` and `|u(psi)| <= 1 - c_eps`. At the bipartition character of a bipartite jump chain `P_psi` has eigenvalues `+-i` of modulus one, and `u(psi) = w(part 1) - w(part 2) = 0`, since a bipartite stationary law gives mass `1/2` to each part. So `exp(T u P_psi) = I` there. Confirmed numerically on the 4-path and the 4-star (Section 5.3). |
| 4 | (S3) Perron gap, simplicity and lower bound on `K` | passed | `P_0(beta,0)` is stochastic, irreducible (graph of `G`), so `1` is simple. If the distance from `1` to the rest of the spectrum tended to `0` along `beta_n -> beta*` in `K`, `1` would be a double eigenvalue at `beta*`. So `r_1 > 0` exists. `Re lambda <= 1 - 2 r_1^2` follows from `|lambda - 1|^2 <= 2 - 2 Re lambda` on the closed unit disc. The eigenvalue `-1` of a periodic chain lies inside `Omega` and causes no trouble, because only `Re zeta` enters `e^{T zeta}`. |
| 5 | Lemma CL, complex Hessian, `O(1/S)`, uniform constants | passed | Rederived (Section 5.2). The only new points against `lem:laplace` are: `det H != 0` and the branch of `det^{-1/2}` on the convex set `{Re H > 0}`; the Gaussian identity extended by the identity theorem from real positive definite `H`; the bound `|e^{-x^T H x/2 + w}| <= e^{-sigma|x|^2/4}` from `Re(x^T H x) = x^T (Re H) x`. All correct. One-dimensional check from scratch: `S rho` converges to the closed-form coefficient `a_0(15 c_3^2/(2h^3) + 3 c_4/h^2) + 3 a_1 c_3/h^2 + a_2/h`, with the residual halving four times per doubling of `S` (Section 5.2). Hypotheses met by S1 to S4: `grad Phi(0) = 0` for every `z` (S4), `Re H_Phi >= sigma_0/2` by continuity from (S4), derivative bounds by Cauchy estimates on the polydisc of Step 1. |
| 6 | Lemma H, two-state case by hand, match with the paper's `C_G` | passed | By hand (Section 5.4): `P_0` is the alternation matrix, `w = (1/2, 1/2)`, `nu(phi) = cos(phi/2)`, `H_Phi = sqrt(tau beta_1 beta_2)/2`, and `det Theta^2 det Sigma_beta / <theta,beta>^2 = tau^2 (2(beta_1 beta_2)^{3/2}/sqrt tau)/(4 tau beta_1 beta_2)` is the same number. The resulting `C_G` equals `(U + V)/(sqrt(4 pi)(tau beta_1 beta_2)^{1/4})` of `lem:L-two` term by term. Numerically `1e-7` (finite differences). The general proof of Lemma H (chain rule at a critical point, `det(I - 1 w'^T) = w_1`) rederived and found correct. |
| 7 | Uniformity of `C` | passed | Every constant traced: `w_min`, `gamma_0`, `sigma_0`, `a_min` from compactness of `K` at `z = 0`; `M_0`, `M_1`, `eps_0`, `z_3`, `B_Phi`, `B_a`, `eps`, `c_eps`, `z_1` from uniform continuity on `K x {|z| <= z_2/2} x polydisc`; `|T| >= c S` from `<theta,beta>` bounded away from `0` (Lemma T). The final `C` depends on `K`, the rates and `mu` only. The one defect is the choice of `z_0` (Section 2). |
| 8 | Irreducibility of `F` and aperiodicity not needed | passed | `c^-, c^+ >= 0` enter only through the affine data `A(z), d(z), mu^(z), e^(z)`; nothing uses `c^+- != 0`. Aperiodicity: see rows 3 and 4. The claim is correct, and `hyp:L` assumes `F` irreducible anyway. |
| 9 | Numerics | passed | The script computes the exact `f^(z)_G(S beta)` by Lemma R (trapezoid rule, exponentially convergent, two grids) and divides by `S^{-(g-1)/2} C_G(beta,z) e^{-S J_G(beta,z)}` with the paper's `C_G` (through `Sigma` of the tilted generator) and `J_G = <d - theta, beta>`. The exponent cancels exactly in the ratio by definition of `J_G`, so the check tests the prefactor and the `O(1/S)` rate. Rerun with `py -I`: output identical to the stored file line by line (`11_rerun_of_10_output.txt`, 11.5 minutes). Two new facets with `g = 4` in Section 5.3. |

## 5. Decisive evidence

### 5.1 Lemma R rederived

Write `D = D_psi`, `K = D^{-1} A`. The matrix `A` has zero diagonal. The entry sum
`mu^T K^{N-1} D^{-1} e` is the sum over words `x_1 ... x_N` with no two equal neighbours of
`mu_{x_1} prod A_{x_l x_{l+1}} e_{x_N} prod_j (theta_j e^{i psi_j})^{-m_j(x)}`, one factor `D^{-1}`
per letter. The scalar `c^n/n!` with `c = sum_j s_j theta_j e^{i psi_j}` expands by the multinomial
formula into `sum_{|k| = n} prod_j (s_j theta_j e^{i psi_j})^{k_j}/k_j!`. With `det D` the term of
`(n, x, k)` carries `prod_j theta_j^{k_j - m_j + 1} e^{i psi_j (k_j - m_j + 1)}`. Integration in
`psi_2, ..., psi_g` keeps `k_j = m_j - 1` for `j >= 2`, and `|k| = n`, `|m| = N = n + g` force
`k_1 = m_1 - 1`. So only words containing every letter survive, each once, and every power of
`theta_j` cancels. Absolute convergence: the sum of the moduli of all terms is at most
`g ||mu||_inf ||D_0^{-1} e||_inf prod |theta_j| sum_n (sum_j s_j |theta_j|)^n (||D_0^{-1}|| ||A||)^{n+g-1}/n!`,
finite for every `theta` with nonzero entries, and independent of `psi`. So Fubini applies and the
formula is exact for all complex radii. No contour condition and no Perron root is used.

### 5.2 Lemma CL in one dimension

Let `Phi(psi) = -(h/2) psi^2 + c_3 psi^3 + c_4 psi^4` with `Re h > 0` and `a(psi) = a_0 + a_1 psi + a_2 psi^2`.
With `psi = x/sqrt S`, `e^{S Phi} = e^{-h x^2/2} e^{w}`, `w = c_3 x^3/sqrt S + c_4 x^4/S`. The terms
of order `S^{-1/2}` are odd. The terms of order `1/S` are
`a_0 (c_3^2 x^6/2 + c_4 x^4) + a_1 c_3 x^4 + a_2 x^2`. Against the normalized Gaussian with
`E x^{2n} = (2n-1)!!/h^n` this gives

    rho_1 = a_0 (15 c_3^2/(2 h^3) + 3 c_4/h^2) + 3 a_1 c_3/h^2 + a_2/h,

so `S rho -> rho_1`. The script integrates on `[-1/2, 1/2]` with `h = 1 + 0.8i`,
`c_3 = 0.3 - 0.1i`, `c_4 = 0.05i`, `a = 1 + 0.4 psi + 0.2i psi^2`. Output: `rho_1 = -0.154162 - 0.251150i`,
and `S rho` equals `-0.156296 - 0.248980i`, `-0.154823 - 0.249387i`, `-0.154499 - 0.250267i`,
`-0.154332 - 0.250708i`, `-0.154248 - 0.250929i`, `-0.154205 - 0.251039i` at
`S = 100, 200, ..., 3200`, with `|S rho - rho_1|` equal to `3.0e-3, 1.9e-3, 9.5e-4, 4.7e-4, 2.4e-4, 1.2e-4`.
The residual halves per doubling, which is the next term `rho_2/S`. The branch of `sqrt h` is the
principal one, which is the branch continuous on `Re h > 0` and positive on the positive axis.
The general statement is the same computation in `m` variables with the bounds of the paper's
`lem:laplace`, and I checked each inequality of the note's proof. The hypotheses of Lemma CL in
Theorem L: `grad Phi(0) = 0` for every `z` by the first-order perturbation identity
`d kappa/d psi_j(0) = -i w_j = -d u/d psi_j(0)`, which I recomputed; `Re H_Phi >= sigma_0/2` by
(S4) and continuity; derivative bounds by Cauchy estimates, since `Phi` and `a` are holomorphic in
`psi` on the polydisc where the Riesz projection is defined.

### 5.3 Two new facets with `g = 4`

Script `11_hypL_audit_check.py`, run as `py -I 11_hypL_audit_check.py`, output
`11_hypL_audit_output.txt`. It imports the note's script for the word series, the torus integral and
the constants, and replaces the note's tilt solver by an independent one (concave Newton in log
coordinates at `z = 0`, then Newton continuation to complex `z` in 40 steps). On the note's face (c)
at `z = 0.08i` the independent solver returns
`theta = (3.541933+0.19478i, 2.583982+0.119692i, 3.125553+0.07874i, 2.858322+0.090933i)`, the
value printed in the note's output to all digits shown.

Two facets with `g = 4` and a bipartite jump chain, both with `mu_i > 0`:

- (e) `G` = the 4-path `0-1-2-3` with rates `2, 1, 1.5, 0.7, 2.2, 1.1`, killing `0.2`, `i` entered
  from `3` and `0` (rates `1.3`, `0.4`), left to `0` and `2` (rates `1.0`, `0.6`),
  `beta = (0.3, 0.2, 0.25, 0.25)`.
- (f) `G` = the 4-star with centre `0`, rates `1, 2, 0.5` out and `1.5, 0.8, 2.5` in, killing `0.1`,
  `i` entered from leaf `1` (rate `1`), left to leaf `3` and the centre (rates `1.2`, `0.3`),
  `beta = (0.35, 0.2, 0.25, 0.2)`.

Results, `z` in `{0, 0.08, 0.08i, -0.06+0.05i}`:

- Lemma R against the word series at `s = 1.2 beta`: relative difference `1e-16` to `4e-15` for real
  and complex radii, at `z = 0` and `z = 0.3 - 0.4i`.
- Tilt residual `< 6e-15`; rows of `P_0` sum to one to `2e-16`; `sum_j w_j = 1`.
- Spectrum of `P_0(beta,0)`: path `1, 0.615, -0.615, -1`; star `1, 0, 0, -1`. Both periodic.
- At the bipartition character (`psi = pi` on one part) the twisted kernel `P_psi` has eigenvalues of
  modulus one (path: two of them; star: two), and `u(psi) = 0` to `1e-16`, so `exp(T Y_psi) = I`.
  The grid scan over `|psi|_inf >= 0.3` gives `max |u(psi)| = 0.988` (path), `0.984` (star), both
  below the (S2) bound `1 - w_min^2 (1 - cos 0.3)`, and the spectral abscissa of `Y_psi` stays at
  most `0.984` and `0.980`.
- Lemma H: `det H_Phi / (det Theta^2 det Sigma / <theta,beta>^2) = 1` to `2.4e-6` (finite differences)
  at every `z`, including complex `z`; `C_spectral = C_paper` to `1e-6`; least eigenvalue of
  `Re H_Phi` between `0.147` and `0.171`.
- Hypothesis L, `S |eps|` at `S = 25 / 400`, two torus grids agreeing to `3e-8` or better:

  | facet | z = 0 | 0.08 | 0.08i | -0.06+0.05i |
  |---|---|---|---|---|
  | (e) 4-path | 0.5442 / 0.5485 | 0.5172 / 0.5209 | 0.5522 / 0.5569 | 0.5305 / 0.5628 |
  | (f) 4-star | 0.8193 / 0.8140 | 0.7742 / 0.7696 | 0.8140 / 0.8088 | 0.8591 / 0.8530 |

  `|eps|` halves at each doubling of `S` and `S eps` settles to a constant, as the theorem predicts,
  on both periodic facets and at complex `z`.

### 5.4 Lemma H for two states by hand

Take `A = [[0, a], [b, 0]]`, `tau = ab`, `beta = (beta_1, beta_2)`. The tilt equations give
`theta_1 = sqrt(tau beta_2/beta_1)`, `theta_2 = sqrt(tau beta_1/beta_2)`, so `<theta,beta> = 2 sqrt(tau beta_1 beta_2)`,
which is the exponent of `lem:L-two`. The Doob matrix is `P_0 = [[0,1],[1,0]]`, periodic with
eigenvalue `-1`, and `w = (1/2, 1/2)`. With `psi = (0, phi)`: `u = (1 + e^{i phi})/2`,
`P_psi = [[0,1],[e^{-i phi},0]]` has eigenvalues `+- e^{-i phi/2}`, the one near `1` is
`kappa = e^{-i phi/2}`, and `nu = u kappa = cos(phi/2)`. So `Phi = 2 sqrt(tau beta_1 beta_2) cos(phi/2)`
and `H_Phi = sqrt(tau beta_1 beta_2)/2`. On the paper's side the tilted generator has rates
`theta_1, theta_2`, and `lem:forest` gives `det Sigma_beta = 2 theta_1 theta_2/(theta_1 + theta_2)^3 = 2 (beta_1 beta_2)^{3/2}/sqrt tau`.
Then `det Theta^2 det Sigma_beta/<theta,beta>^2 = tau^2 (2 (beta_1 beta_2)^{3/2}/sqrt tau)/(4 tau beta_1 beta_2) = sqrt(tau beta_1 beta_2)/2`.
Lemma H holds. Then `C_G = (2 pi)^{-1/2} H_Phi^{-1/2} (mu . r)(l . e) tau/<theta,beta>`, and with
`r = (1, theta_1/a)`, `l = beta/r` the product `(mu . r)(l . e) sqrt tau/sqrt(beta_1 beta_2)` expands
to `p_1 e_1 sqrt(tau beta_1/beta_2) + p_1 a e_2 + p_2 b e_1 + p_2 e_2 sqrt(tau beta_2/beta_1) = U + V`,
so `C_G = (U + V)/(sqrt(4 pi)(tau beta_1 beta_2)^{1/4})`, the constant of `lem:L-two`. The script
confirms both identities to `1e-7` (finite differences) with `a = 1.7`, `b = 0.6`, `beta = (0.35, 0.65)`.

### 5.5 Points rechecked in Theorem L

- Lemma T. The tilt system `grad_b Lambda_0(b,z) = -beta'` has Jacobian `Sigma_beta`, positive
  definite by `lem:perron`; the holomorphic implicit function theorem applies with `beta` as a
  real-analytic parameter; uniform `z_2` by a finite cover of `K`. Real for real `z` by
  conjugation and uniqueness. For real `z >= 0` the branch is the Perron root by the open-and-closed
  argument, so `r, l > 0` and `theta` is the tilt of `def:tilt` for `A(z)`; the paper's criterion
  in the proof of `prop:rate` (maximizer if and only if `beta` is stationary for the tilted
  generator) gives `J_G(beta,z) = <d(z) - theta, beta>`. For real `z < 0`, `A(z)` may have negative
  off-diagonal entries (the 3-path with `c^-_1 c^+_3 > 0`), but `hyp:L` asks for the identification
  only on `z >= 0` and for reality on the real axis, which conjugation gives.
- Lemma D. `P_0 1 = 1`, `w^T P_0 = w^T`, `R^{-1} K_psi R = E_psi P_0` checked.
- Step 1. The contour `Gamma` is at distance `gamma_0/2` from `1` and from the chord, `delta_1`
  from the arc, for every `beta` in `K`; `M_0` is finite. The rank of the Riesz projection is one
  on the connected set polydisc times disc for each `beta`.
- Step 3. `Re(e^{i arg T} zeta) <= Re zeta + |zeta| |arg T|`, which gives the stated
  `1 - 0.45 gamma_0`; the comparison with `e^{Re T}` uses `1 - cos(arg T) <= (arg T)^2/2`.
- Step 4. For real `psi`, `||E_psi P_0(beta,z)|| = ||P_0(beta,z)|| <= 1 + c_eps/8`; the bound
  `||exp(T Y)|| <= exp(|T| |u| ||P||)` gives `|I_3| <= C e^{Re T} e^{-3 c_eps |T|/8}`.
- Step 6. The relative error is `rho/a(0)` plus terms `C S^{(g-1)/2} e^{-c' S}`, all `<= C/S` for
  `S >= 1`.
- Step 7. `C_G` real for real `z` because `H_Phi` is real (from `nu(-psi) = conj nu(psi)`), and the
  branch of `det^{-1/2}` is positive on real positive definite matrices.

## 6. Remaining gap

None in the mathematics. The editorial correction: in Step 6 of Theorem L replace
`z_0 = min(z_1, z_2/2)` by `z_0 = min(z_1, z_3/2)`. With the printed choice, Step 7 asserts the
holomorphy of `nu`, the bound `Re H_Phi >= sigma_0/2` and the continuity of the branch of
`det^{-1/2}` on `|z| < 2 z_0`, but Step 1 secures them only on `|z| <= z_3`, and `2 z_1` may exceed
`z_3`.

Two remarks on the note that do not affect the verdict. The sentence in (S2) that the bound holds
"because the holding times are exponential" is interpretation; what the proof uses is the elementary
inequality for `|sum_j w_j e^{i psi_j}|`, which is part of the exact formula. The note's tilt
solver (`solve_tilt` started from `theta = row sums`) fails with a singular Newton matrix on the
4-path facet; this is a start-point issue of the script, not of the proof, and an independent
solver (concave Newton in log coordinates, then continuation in `z`) reproduces the note's tilt on
its face (c) and solves the new facets to residual below `1e-14`.

## 7. Strongest safe statement

Hypothesis `hyp:L` (equivalently, the conclusion of `lem:L-two` required in `rem:layer-four`) holds
for every `G` satisfying (H) with `|G| >= 2`, every `i` outside `G` with `c^-, c^+ >= 0` (irreducibility
of `F` is not needed), every `mu_i >= 0`, and every compact `K` in the open simplex on `G`, with
`J_G(beta,z) = <d(z) - theta(beta,z), beta>` and
`C_G(beta,z) = (2 pi)^{-(g-1)/2} det H_Phi(beta,z)^{-1/2} (mu^(z) . r)(l . e^(z)) det Theta/<theta,beta>`,
which for real `z >= 0` is the constant of Section `sec:layer-setting`. The radius `z_0` is not
explicit. With this, Theorem `thm:layer` holds for every `k >= 2` with the same proof. The cheapest
next check before the paper is edited is a second reading of Lemma CL's constant bookkeeping and of
the choice of `z_0`; both are small.
