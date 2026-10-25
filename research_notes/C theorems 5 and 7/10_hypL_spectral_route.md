# Hypothesis L by the spectral route (Nagaev and Guivarc'h)

Date October 24, 2026. Base checkpoint commit `0ffc041`. Write scope: this file and the files
`10_*` in this folder. No paper file was edited.

Inputs read. In `kagey-problems/problem131/paperC`: `sec_boundary.tex` in full, `app_torus.tex`
(Lemma `lem:perron`, Proposition `prop:constant`(a), Lemma `lem:torus`, the proof of
Theorem `thm:local`), `app_laplace.tex` (Lemma `lem:laplace`, Remark `rem:laplace-uniform`). In
`research_notes`: `C theorems 5 and 7/08_T2_boundary_layer.md`, `Paper C audits/04_boundary_layer_T2.md`
(Section 5 on Lemma L), and item 3 of "Other mathematical concerns" in
`Paper C audits/10_external_referee_report.md`.

Scripts. `10_hypL_spectral_check.py`, run as `py -I 10_hypL_spectral_check.py`, output
`10_hypL_spectral_output.txt`.

## 0. The statement attacked

Hypothesis `hyp:L` (`sec_boundary.tex`, line 366). Let `G` satisfy (H) with `g = |G| = k-1 >= 2`,
let `i` not in `G` with `F = G + {i}` irreducible, and let `K` be a compact subset of the open
simplex on `G`. There are `z_0 > 0`, `C`, and functions `J_G(beta,z)`, `C_G(beta,z)` on
`K x {|z| < 2 z_0}`, holomorphic in `z`, jointly continuous, real for real `z`, equal to the rate
and the local-law constant of Section `sec:layer-setting` for real `0 <= z < 2 z_0`, with
`C_G(beta,0) = C_G(beta) > 0`, such that uniformly for `beta` in `K`, `S >= 1` and complex
`|z| <= z_0`

    f^(z)_G(S beta) = S^{-(g-1)/2} C_G(beta,z) e^{-S J_G(beta,z)} (1 + eps),   |eps| <= C/S.

Here `f^(z)_G` is the word series of Lemma `lem:layer-exact`:

    f^(z)_G(s) = e^{-<d(z),s>} sum_{m >= 1} W_z(m) prod_j s_j^{m_j-1}/(m_j-1)!,
    W_z(m) = sum_w mu^(z)_{w_1} prod_l A(z)_{w_l w_{l+1}} e^(z)_{w_last},

with `A(z) = A_G + z offdiag(c^- (c^+)^T)`, `d(z) = q_G - z c^- o c^+`,
`mu^(z) = mu_G + z mu_i c^+`, `e^(z) = 1 + z c^-`.

## 1. Is the quantity of Markov additive form?

Yes, but not in the obvious way, and the obvious way fails. This is the first finding.

The obvious form. `f^(z)_G(s)` is the density of the occupation vector `L(S)` of the
(complex-weighted) chain with generator `Q_G(z)`. The pair `(X_t, L_t)` is a continuous-time
Markov additive process, and

    E[e^{<eta, L(S)>} e(X_S)] = mu^T exp(S (Q_G(z) + diag eta)) e .

Fourier inversion over `eta = theta + i xi`, `xi` in `R^{g-1}`, does not converge absolutely. The
law of `L(S)` has atoms at the vertices (no jump) and densities on every lower face. Even the part
on the open face does not help: `f_G` restricted to the open simplex has jumps at its boundary
(for `g = 2`, `f_G(s_1, S - s_1)` tends to `mu_1 q_12 e^{-q_2 S} > 0` as `s_1 -> 0`), so its
Fourier transform decays like `1/|xi|` and is not integrable. A proof along this line needs a
smoothing argument with control of the boundary terms. We do not take it.

The form that works. Put the Fourier variable on the jump chain instead. The holding times are
exponential, so the Laplace variables live on circles, and the characters form the compact torus
`T^{g-1}`. After one exact residue in the diagonal direction, the integrand is a matrix
exponential of a Fourier-twisted jump kernel. At the right (complex) radii this kernel is, after a
Doob transform, a matrix with row sums one, stochastic at `z = 0`. That is the
Nagaev and Guivarc'h setting. Lemma R below states the representation. It is exact, absolutely
convergent, and valid for every choice of radii, real or complex, so no contour deformation is
used anywhere.

## 2. Notation

Number the states of `G` as `1, ..., g`. For `theta` in `(C \ {0})^G` and `psi` in `R^G` with
`psi_1 = 0` (we identify such `psi` with a point of `T^{g-1}`) put

    D_psi = diag(theta_j e^{i psi_j}),   K_psi = D_psi^{-1} A(z),   c_psi(s) = sum_j s_j theta_j e^{i psi_j}.

Norms: `||.||` is the max-row-sum norm on matrices and the max norm on vectors, `|psi|_inf` is the
max of `dist(psi_j, 2 pi Z)`, and `|x|` is the Euclidean norm.

## 3. The exact representation

**Lemma R.** For every `z` in `C`, every `theta` in `(C \ {0})^G` and every `s` in `(0,inf)^G`,

    f^(z)_G(s) = e^{-<d(z),s>} (2 pi)^{-(g-1)} int_{T^{g-1}} mu^(z)T K_psi^{g-1} exp(c_psi(s) K_psi) D_psi^{-1} e^(z) det D_psi  dpsi .

*Proof.* Write `A = A(z)`, `mu = mu^(z)`, `e = e^(z)`. Expand the exponential. The integrand is

    sum_{n >= 0} (c_psi^n / n!) mu^T K_psi^{n+g-1} D_psi^{-1} e det D_psi .

Since `A` has zero diagonal, `mu^T K_psi^{N-1} D_psi^{-1} e` is the sum over the words
`x_1 ... x_N` in `G` with no two equal neighbours of
`mu_{x_1} prod_{l<N} A_{x_l x_{l+1}} e_{x_N} prod_j (theta_j e^{i psi_j})^{-m_j(x)}`, where `m_j(x)`
is the number of letters `j`. The multinomial formula gives
`c_psi^n/n! = sum_{|k| = n} prod_j (s_j theta_j e^{i psi_j})^{k_j}/k_j!`. All these series are
dominated by `sum_n (sum_j |s_j theta_j|)^n/n! * ||mu|| (||D_0^{-1}|| ||A||)^{n+g-1} ||D_0^{-1} e|| prod |theta_j|`,
which is finite and does not depend on `psi`. So we may integrate term by term. The term of
`(n, x, k)` carries `prod_j theta_j^{k_j - m_j + 1} e^{i psi_j (k_j - m_j + 1)}`. Integration over
`psi_2, ..., psi_g` keeps exactly the terms with `k_j = m_j - 1` for `j >= 2`. Then
`k_1 = n - sum_{j>=2}(m_j - 1) = n + (g-1) - (N - m_1) = m_1 - 1`, because `N = n + g`. So only
words with every letter survive, each for exactly one `n` (namely `n = N - g >= 0`) and one `k`,
and in them every power of `theta_j` cancels. What is left is
`sum_x mu_{x_1} prod A e_{x_N} prod_j s_j^{m_j-1}/(m_j-1)!`, and grouping by `m` gives
`sum_m W_z(m) prod_j s_j^{m_j-1}/(m_j-1)!`. ∎

For `g = 1`, `K = 0` and the lemma gives `f = e^{-d s} mu e`, as in the paper. The lemma is the
torus formula of `lem:torus` with the circle of the diagonal direction integrated out by the
functional calculus instead of the Schur complement: with `w = e^{i psi_0}` the full `g`-torus
integrand is `e^{w c} w^{g-1} mu^T (w - K_psi)^{-1} D_psi^{-1} e det D_psi`, and Cauchy's formula
on `|w| = r > rho(K_psi)` gives `F(K_psi)` with `F(w) = w^{g-1} e^{wc}`. The direct proof above
avoids any condition on the radii. Part 1 of the script checks Lemma R against the word series.

## 4. The complex tilt and the Doob transform

**Lemma T (the tilt continued to complex z).** There are `z_2 > 0` and functions
`theta(beta,z)`, `r(beta,z)`, `l(beta,z)` in `C^G` on `K x {|z| < z_2}`, jointly continuous,
holomorphic in `z`, such that

    (A(z) - diag theta) r = 0,   l^T (A(z) - diag theta) = 0,   l o r = beta,

the eigenvalue `0` of `A(z) - diag theta` is simple, and `theta_j`, `r_j`, `<theta, beta>` stay in
a fixed compact set away from `0`. For real `z` in `[0, z_2)` they are real, `r, l > 0`, and
`theta(beta,z)` is the tilt of Definition `def:tilt` for the irreducible Metzler matrix `Q_G(z)`.
Conjugation maps the solution at `z` to the solution at `conj z`.

*Proof.* For `vartheta` near `theta(beta,0)` and `z` near `0` let `lambda(vartheta,z)` be the
eigenvalue of `A(z) - diag vartheta` near `0`. At `z = 0` it is the Perron root, a simple
eigenvalue, so by analytic perturbation of a simple eigenvalue `lambda` and normalized eigenvectors
are holomorphic in `(vartheta, z)`. First-order perturbation gives
`d lambda/d vartheta_j = -l_j r_j/(l . r)`, and `lambda(vartheta + t 1, z) = lambda(vartheta, z) - t`.
Write `vartheta = (0, b) + t 1` with `b` in `C^{g-1}` and put `Lambda_0(b, z) = lambda((0,b), z)`.
The tilt equations are `grad_b Lambda_0(b,z) = -beta'` and `t = Lambda_0(b,z)`. At `z = 0`,
`Lambda_0(., 0)` is the function of the same name in the proof of Proposition `prop:constant`(a)
for the face `G`, up to the change of variable `vartheta -> q - vartheta`, which flips the sign of
the argument twice in the Hessian. So the Jacobian `grad_b^2 Lambda_0` at the real tilt is
`Sigma_beta`, which is positive definite by Lemma `lem:perron`. The holomorphic implicit function
theorem gives `b(beta,z)`, holomorphic in `z` and real-analytic in `beta`, near each `(beta_0, 0)`,
and unique in a ball around `b(beta_0, 0)`. Cover `K` by finitely many such neighbourhoods. On
overlaps the solutions agree at `z = 0` and by uniqueness in the balls for small `z`. This gives a
uniform `z_2`. Normalize `l . r = 1`. Then `l o r = beta` holds in all coordinates, since both sides
sum to `1`. Simplicity and the bounds away from `0` hold at `z = 0` (`theta > 0` by `eq:A-radii`,
`r, l > 0`), so they hold for `|z|` small by continuity. If `(theta, r, l)` solves the equations at
`z`, then the conjugates solve them at `conj z`, because `A(conj z) = conj A(z)`. By uniqueness the
solution is real for real `z`. For real `z` the branch `lambda` is the Perron root: the set of real
`z` where the two agree is open (a simple Perron root is the only eigenvalue in a small disc) and
closed, and it contains `0`. So `r` and `l` can be taken positive, and `theta` is a tilt of
`Q_G(z)` with stationary law `beta`, which by Definition `def:tilt` is unique. ∎

From now on `theta = theta(beta,z)`, `r`, `l` are these functions, `R = diag r`,
`Theta = diag theta`, and

    P_0 = R^{-1} Theta^{-1} A(z) R,   w = theta o beta / <theta, beta>,   E_psi = diag(e^{-i psi_j}),   P_psi = E_psi P_0 .

**Lemma D (Doob transform).** `P_0 1 = 1`, `w^T P_0 = w^T`, `w . 1 = 1`, and
`R^{-1} K_psi R = P_psi`. At `z = 0`, `P_0` is a stochastic matrix with zero diagonal whose graph is
the graph of `G`, so it is irreducible, and `w > 0`.

*Proof.* `(P_0 1)_j = (Theta^{-1} A r)_j / r_j = 1` since `A r = Theta r`. Next
`(theta o l o r)^T R^{-1} Theta^{-1} A R = (l o theta)^T Theta^{-1} A R = l^T A R = (theta o l)^T R = (theta o l o r)^T`,
and `l o r = beta`. Diagonal matrices commute, so `R^{-1} D_psi^{-1} A R = E_psi R^{-1} Theta^{-1} A R`.
At `z = 0` all entries are nonnegative and the row sums are one. ∎

With `c_psi(S beta) = S <theta,beta> u(psi)`, `u(psi) = sum_j w_j e^{i psi_j}`, Lemma R at
`s = S beta` and these radii reads

    f^(z)_G(S beta) = e^{-S <d,beta>} (2 pi)^{-(g-1)} int_{T^{g-1}} mut^T P_psi^{g-1} exp(T Y_psi) et_psi det D_psi dpsi,   (4.1)

    T = S <theta, beta>,   Y_psi = u(psi) P_psi,   mut = R mu^(z),   et_psi = R^{-1} D_psi^{-1} e^(z).

`T` is complex for complex `z`, with `|arg T| = |arg <theta,beta>| = O(|z|)`. Note
`e^{-S<d,beta>} e^T = e^{-S J}` with `J = <d - theta, beta>`.

## 5. Spectral facts at z = 0

Fix `beta` in `K` and `z = 0`. All constants below are uniform on `K` by continuity and
compactness. Let `w_min = min_{K, j} w_j(beta, 0) > 0`.

**(S1) Norm bound.** For real `psi`, `|P_psi| = P_0` entrywise, so `||P_psi|| = 1`, the spectral
radius of `P_psi` is at most `1`, and `||exp(T Y_psi)|| <= exp(T |u(psi)|)`.

**(S2) Non-lattice bound for the holding-time characters.** If `|psi|_inf >= epsilon` then

    |u(psi)| <= 1 - w_min^2 (1 - cos epsilon).

Indeed `|u|^2 = 1 - sum_{j,k} w_j w_k (1 - cos(psi_j - psi_k))`, and if
`dist(psi_k, 2 pi Z) >= epsilon` for some `k >= 2`, the pairs `(1,k)` and `(k,1)` give at least
`2 w_min^2 (1 - cos epsilon)`, since `psi_1 = 0`. Then use `sqrt(1 - x) <= 1 - x/2`.

**(S3) Gap of the Doob kernel.** The eigenvalue `1` of `P_0` is simple (Perron and Frobenius). Every
other eigenvalue `lambda` has `|lambda| <= 1` and `lambda != 1`. By continuity of the spectrum and
compactness of `K` there is `r_1 > 0` with `|lambda - 1| >= 2 r_1` for all of them and all `beta`
in `K`. Since `|lambda - 1|^2 <= 2 - 2 Re lambda` in the unit disc, `Re lambda <= 1 - gamma_0` with
`gamma_0 = 2 r_1^2 > 0`.

No aperiodicity is needed. The jump chain may be periodic (the path of three states and the
4-cycle are bipartite, and their `P_0` has the eigenvalue `-1`, see Part 2 of the output). The
reason is that the time enters through `exp(T Y)`, a continuous-time semigroup, so only real parts
of eigenvalues matter. The non-lattice condition of the additive part is (S2), and it holds for
every face because the holding times are exponential.

**(S4) The Perron branch and its Hessian.** For complex `psi` near `0`, let `kappa(psi)` be the
eigenvalue of `P_psi` near `1` and `nu(psi) = u(psi) kappa(psi)` the eigenvalue of `Y_psi` near `1`.
Then `nu(0) = 1` and `grad nu(0) = 0`, for every `z` (not only `z = 0`): first-order perturbation
with left vector `w` and right vector `1` gives
`d kappa/d psi_j (0) = w^T (-i e_j e_j^T) P_0 1 = -i w_j`, and `d u/d psi_j (0) = i w_j`.
At `z = 0` the Hessian `N = grad^2 nu(0)` (in the coordinates `psi_2, ..., psi_g`) is real, and

    -N >= V_w,   psi^T V_w psi = (1/2) sum_{j,k} w_j w_k (psi_j - psi_k)^2 >= w_min^2 |psi|^2   (psi_1 = 0).

*Proof.* For real `psi`, `E_{-psi} P_0 = conj(E_psi P_0)` and `u(-psi) = conj u(psi)`, so
`nu(-psi) = conj nu(psi)`. Comparing Taylor coefficients of order two shows that `N` is real. By
(S1), `|kappa(psi)| <= 1`, so `Re nu(psi) <= |nu(psi)| <= |u(psi)|`. Now
`Re nu(psi) = 1 + (1/2) psi^T N psi + O(|psi|^3)` and
`|u(psi)| = (1 - psi^T V_w psi + O(|psi|^4))^{1/2} = 1 - (1/2) psi^T V_w psi + O(|psi|^4)`. So
`psi^T (-N - V_w) psi >= O(|psi|^3)` for small real `psi`, and scaling `psi` gives `-N >= V_w`. The
lower bound for `V_w` keeps only the pairs `(1,k)` and `(k,1)`. ∎

So the phase `Phi(psi) = <theta,beta> nu(psi)` has a nondegenerate critical point at `psi = 0`
with critical value `<theta,beta>` and Hessian `-H_Phi`, where at `z = 0`

    H_Phi = <theta,beta> (-N) >= sigma_0 I,   sigma_0 = min_K <theta(beta,0),beta> w_min^2 > 0 .

This replaces hypotheses (ii) and (iii) of Lemma `lem:laplace` by spectral facts.

## 6. A Laplace lemma on a cube with a complex Hessian

The phase is complex for complex `z`, so we need the Laplace lemma with a complex symmetric
Hessian whose real part is positive definite. With the critical point already on the domain of
integration (Lemma T did that, by choosing the radii), the proof of `lem:laplace` goes through. We
write it out.

**Lemma CL.** Let `m >= 1`, `epsilon_0` in `(0,1]`, `P` a set, and `Phi, a : P x [-epsilon_0,epsilon_0]^m -> C`
with `psi`-derivatives of `Phi` of orders `2` to `4` bounded by `B_Phi` and of `a` of orders `0` to
`2` bounded by `B_a`. Assume `grad Phi(p,0) = 0` and that `H(p) = -grad^2 Phi(p,0)` (complex
symmetric) has `Re H(p) >= sigma I`. Let `epsilon = min(epsilon_0, 3 sigma/(2 m^3 B_Phi))`. Then for
`S >= 1`

    int_{[-epsilon,epsilon]^m} e^{S Phi(p,psi)} a(p,psi) dpsi
        = e^{S Phi(p,0)} (2 pi/S)^{m/2} det H(p)^{-1/2} (a(p,0) + rho),   |rho| <= C/S,

with `C` depending only on `m, sigma, B_Phi, B_a, epsilon_0`. The branch of `det^{-1/2}` is the one
that is continuous on the convex set `{H symmetric, Re H > 0}` and positive on real positive
definite `H`.

*Proof.* The set is convex, and `det H != 0` on it: if `H v = 0` with `v != 0`, then
`conj(v)^T H v = conj(v)^T (Re H) v + i conj(v)^T (Im H) v` has positive real part. So the branch
exists. The function `H -> int_{R^m} e^{-x^T H x/2} dx` is holomorphic in the entries on this set
(dominated convergence, `|e^{-x^T H x/2}| = e^{-x^T (Re H) x/2}`), and it equals
`(2 pi)^{m/2} det H^{-1/2}` on real positive definite `H`, a totally real set of full dimension. By
the identity theorem the two agree on the whole set.

Taylor's theorem with integral remainder gives
`Phi(psi) - Phi(0) + psi^T H psi/2 = R(psi)` with `R = (1/6) Phi_{abc} psi^a psi^b psi^c + omega_0`,
`|omega_0| <= C |psi|^4`, and `|R| <= (m^3/6) B_Phi |psi|_inf^3 <= (m^3/6) B_Phi epsilon |psi|^2 <= (sigma/4)|psi|^2`
on the cube. Substitute `psi = x/sqrt(S)` and put `w(x) = S R(x/sqrt S)`. Then `|w| <= sigma |x|^2/4` and

    |e^{-x^T H x/2 + w(x)}| <= e^{-sigma |x|^2/2 + sigma |x|^2/4} = e^{-sigma |x|^2/4}.

From here the proof of `lem:laplace` applies word for word: `w = S^{-1/2} P(x) + omega_1` with `P`
the cubic form and `|omega_1| <= C |x|^4/S`, so
`e^{w} a(x/sqrt S) = a_0 + S^{-1/2}(a_0 P(x) + a_j x^j) + omega(x)` with
`|omega| <= C S^{-1} (1+|x|)^6 e^{sigma |x|^2/4}`. Against the weight `e^{-x^T H x/2}` the term `omega`
contributes `O(1/S)`, by the bound above. The odd polynomial integrates to `0` over `R^m`, because
the weight is even. Extending the two other integrals from the cube `|x|_inf <= epsilon sqrt S` to
`R^m` costs `O(e^{-sigma epsilon^2 S/4})`. The Gaussian integral is `(2 pi)^{m/2} det H^{-1/2}`. Since
`|det H| <= (m B_Phi)^m`, all errors are `O(1/S)` relative to `(2 pi/S)^{m/2} |det H|^{-1/2}`. ∎

## 7. The theorem

**Theorem L.** Let `G` satisfy (H) with `g = |G| >= 2`, let `c^-, c^+` be any nonnegative vectors
on `G`, `mu_i >= 0`, and `K` a compact subset of the open simplex on `G`. Put

    J_G(beta,z) = <d(z) - theta(beta,z), beta>,
    C_G(beta,z) = (2 pi)^{-(g-1)/2} det H_Phi(beta,z)^{-1/2} (mu^(z) . r)(l . e^(z)) det Theta / <theta, beta>,

with `theta, r, l` from Lemma T (`l . r = 1`) and `H_Phi = -grad^2_psi Phi(0)`,
`Phi(psi) = <theta,beta> nu(psi)` as in (S4). There are `z_0 > 0` and `C` such that the conclusion
of Hypothesis `hyp:L` holds with these functions. In particular `hyp:L` holds for every face with
`k >= 4` states that satisfies the standing assumptions of Theorem `thm:layer`.

*Proof.* Step 1 (domains and constants). By Lemma T, (S3), (S4) and continuity, choose
`epsilon_0 > 0` and `z_3 <= z_2` such that for `beta` in `K`, `|z| <= z_3` and complex `psi` with
`|psi_j| <= 2 epsilon_0`:

- the matrices `Y_psi` satisfy `||Y_psi - P_0(beta,0)|| <= 1/(2 M_0)`, where `M_0` is the maximum of
  `||(zeta - P_0(beta,0))^{-1}||` over `beta` in `K` and `zeta` on the contour `Gamma = boundary of Omega`,
  `Omega = {|zeta| <= 1 + delta_1, Re zeta <= 1 - gamma_0/2}`, `delta_1 = gamma_0/8`. (`M_0` is
  finite: by (S3) the spectrum of `P_0(beta,0)` avoids `Gamma`, and `Gamma x K` is compact.) Then
  `(zeta - Y_psi)^{-1}` exists on `Gamma` with norm at most `2 M_0`, the Riesz projection
  `Pi_psi = I - (2 pi i)^{-1} oint_Gamma (zeta - Y_psi)^{-1} dzeta` has rank one (its rank is
  continuous, and it is one at `psi = 0, z = 0`), and `nu(psi)`, the one eigenvalue of `Y_psi`
  outside `Omega`, is holomorphic in `psi` and `z`;
- `u(psi) != 0`, and `nu`, `kappa = nu/u`, `Pi_psi`, `D_psi`, `et_psi` are bounded by a constant `M_1`;
- `Re H_Phi(beta,z) >= (sigma_0/2) I` (continuity from (S4));
- `|arg <theta,beta>| <= gamma_0/40`, and `|a(0)| >= a_min/2` where
  `a(psi) = kappa(psi)^{g-1} mut^T Pi_psi et_psi det D_psi` and `a_min = min_K a(0)|_{z=0} > 0`.

The last minimum is positive: at `z = 0`, `Pi_0 = 1 w^T`, so
`a(0) = (mu_G . r)(l . 1) det Theta/<theta,beta>`, and `mu_G . r > 0` by (H), `l, r, theta > 0`.
In general `a(0) = (mu^(z) . r)(l . e^(z)) det Theta/<theta,beta>`, by `Pi_0 = 1 w^T` and
`w_j/(r_j theta_j) = l_j/<theta,beta>`.

Cauchy estimates on the polydisc of radius `epsilon_0` around each point of the real cube
`[-epsilon_0, epsilon_0]^{g-1}` bound the derivatives of `Phi = <theta,beta> nu` and of `a` up to order four by
constants `B_Phi`, `B_a`. Lemma CL with `sigma = sigma_0/2` fixes `epsilon <= epsilon_0`. Then (S2)
fixes `c_epsilon = w_min^2 (1 - cos epsilon)`. Finally choose `z_1 <= z_3` so that for `|z| <= z_1`
and real `psi`: `sum_j |w_j(beta,z) - w_j(beta,0)| <= c_epsilon/8`,
`||P_0(beta,z)|| <= 1 + c_epsilon/8`, and `1 - cos(arg T) <= c_epsilon/8`.

Step 2 (split). Split the torus in (4.1) into the cube `Q = {|psi|_inf <= epsilon}` and its
complement, and on `Q` write `exp(T Y) = e^{T nu} Pi + exp(T Y)(I - Pi)`. Since `P_psi` commutes
with `Y_psi`, `P_psi^{g-1} Pi_psi = kappa^{g-1} Pi_psi`. So

    int_{T^{g-1}} mut^T P_psi^{g-1} exp(T Y_psi) et_psi det D_psi dpsi = I_1 + I_2 + I_3,
    I_1 = int_Q e^{S Phi(psi)} a(psi) dpsi,
    I_2 = int_Q mut^T P_psi^{g-1} exp(T Y_psi)(I - Pi_psi) et_psi det D_psi dpsi,
    I_3 = int_{T^{g-1} \ Q} mut^T P_psi^{g-1} exp(T Y_psi) et_psi det D_psi dpsi .

The leading size is `|e^{S Phi(0)}| = |e^T| = e^{Re T}`, with `Re T = |T| cos(arg T)`.

Step 3 (the non-Perron part near the identity character). By the Riesz formula
`exp(T Y)(I - Pi) = (2 pi i)^{-1} oint_Gamma e^{T zeta} (zeta - Y)^{-1} dzeta`. On `Gamma`,
`Re(T zeta) = |T| Re(e^{i arg T} zeta) <= |T| (1 - gamma_0/2 + (1 + delta_1)|arg T|) <= |T|(1 - gamma_0/2 + gamma_0/20)`.
So `|I_2| <= C exp(|T|(1 - 0.45 gamma_0))`, and with `1 - cos(arg T) <= (arg T)^2/2 <= gamma_0/40`,
`|I_2| <= C e^{Re T} e^{-gamma_0 |T|/3}`.

Step 4 (away from the identity character). For real `psi` with `|psi|_inf >= epsilon`, by (S2) and
the choice of `z_1`, `|u(psi)| <= 1 - c_epsilon + c_epsilon/8` and `||P_psi|| = ||P_0|| <= 1 + c_epsilon/8`.
So `||exp(T Y_psi)|| <= exp(|T| (1 - c_epsilon/2))`, and with `1 - cos(arg T) <= c_epsilon/8`,
`|I_3| <= C e^{Re T} e^{-c_epsilon |T|/4}`.

Step 5 (expansion at the identity character). By Lemma CL with `m = g - 1`,
`I_1 = e^T (2 pi/S)^{(g-1)/2} det H_Phi^{-1/2} (a(0) + rho)`, `|rho| <= C/S`.

Step 6 (assembly). `e^{-S<d,beta>} e^T = e^{-S J}`, so

    f^(z)_G(S beta) = S^{-(g-1)/2} C_G(beta,z) e^{-S J_G(beta,z)} (1 + eps),
    eps = rho/a(0) + (I_2 + I_3) / (e^T (2 pi/S)^{(g-1)/2} det H_Phi^{-1/2} a(0)).

The first term is at most `2C/(a_min S)`. In the second, `|det H_Phi|^{1/2} <= (g B_Phi)^{(g-1)/2}`
and `|T| >= c S`, so it is at most `C S^{(g-1)/2} e^{-c' S} <= C/S`. All constants depend only on
`K`, the rates, `mu` and the choices above. Set `z_0 = min(z_1, z_2/2)`.

Step 7 (the properties of `J_G` and `C_G`). Holomorphy in `z` and joint continuity follow from
Lemma T and from the holomorphy of `nu` (Step 1), since `H_Phi` is a second derivative at `psi = 0`
and the branch of `det^{-1/2}` is continuous where `Re H_Phi > 0`. For real `z`, conjugation
symmetry (Lemma T and `nu(-psi) = conj nu(psi)`) makes `H_Phi` real, so `J_G` and `C_G` are real.
`J_G(beta,z) = <d(z) - theta(beta,z), beta>` is the rate of `Q_G(z)` for real `z`, because
`theta` is its tilt (Lemma T) and the rate of an irreducible Metzler matrix is `<q - theta, alpha>`
(Proposition `prop:rate`, used in this form at the end of the proof of `thm:local`). For the
constant we use the determinant identity of Section 8:
`det H_Phi = det Theta^2 det Sigma_beta(z) / <theta,beta>^2` for real `z`. It gives
`C_G(beta,z) = (mu^(z) . r)(l . e^(z)) / ((2 pi)^{(g-1)/2} sqrt(det Sigma_beta(z)))`, which is the
constant of Section `sec:layer-setting`. At `z = 0` it is `C_G(beta) > 0`. ∎

## 8. The determinant identity

**Lemma H.** For real `z` in `[0, z_2)`, `det H_Phi = det Theta^2 det Sigma_beta(z) / <theta,beta>^2`.

*Proof.* Set `z(psi) = kappa(psi) theta o e^{i psi}`. Then `Phi(psi) = sum_j beta_j z_j(psi)`, and
`det(diag z(psi) - A) = det D_psi det(kappa - K_psi) = 0`. Near `theta` the eigenvalue
`lambda(vartheta) = lambda(vartheta, z)` of Lemma T is the only eigenvalue of `A - diag vartheta`
near `0`, so `lambda(z(psi)) = 0`. Since `d lambda/d vartheta_1 = -beta_1 != 0`, the zero set of
`lambda` near `theta` is a graph `vartheta_1 = g(vartheta')`, and `g` is the function `g` of
Lemma `lem:torus` for `A(z)` (it satisfies `lambda(g(z'), z') = 0` for real `z'` near `theta'`, as
shown in the proof of `thm:local`, and both are holomorphic). So
`Phi(psi) = Psi_c(z'(psi))` with `Psi_c(z') = beta_1 g(z') + sum_{j>=2} beta_j z_j`. The proof of
`thm:local` gives `grad Psi_c(theta') = 0` and `grad^2 Psi_c(theta') = B^T Sigma_beta B` with
`det B = 1/beta_1` (paragraphs "Hypotheses (i) and (ii)", applied to `A(z)`, which is nonnegative
off the diagonal and irreducible). By (S4), `d kappa/d psi_k (0) = -i w_k`, so for `j, k >= 2`,
`d z_j/d psi_k (0) = i theta_j (delta_jk - w_k)`. The chain rule at a critical point gives
`H_Phi = (I - w' 1^T) Theta' B^T Sigma_beta B Theta' (I - 1 w'^T)`, and
`det(I - 1 w'^T) = 1 - sum_{k>=2} w_k = w_1 = theta_1 beta_1/<theta,beta>`. Multiply. ∎

Part 3 of the script checks Lemma H, also at complex `z` (where both sides are holomorphic and so
agree by the identity theorem).

## 9. Hypotheses used, checked against the paper

| What the proof uses | Where it comes from |
|---|---|
| `G` irreducible, `g >= 2` | (H) for `G` in `hyp:L`. Gives `theta > 0`, the simple Perron root, `P_0` irreducible. |
| `mu(G) > 0` | (H). Gives `a(0) > 0` at `z = 0`, so `C_G(beta,0) > 0` and the relative error. |
| `beta` in a compact subset of the open simplex | `hyp:L`. Gives `w_min > 0`, the tilt, uniform constants. |
| `F` irreducible | Not used. `c^-, c^+ >= 0` arbitrary is enough. |
| Aperiodicity of the jump chain | Not needed (S3). |
| Non-lattice condition | Automatic (S2), from exponential holding times. |
| `z` small | `z_0` depends on `K` and the rates through `gamma_0`, `sigma_0`, `w_min`, `a_min` and the continuity moduli. It is not explicit. |

The paper results cited: Lemma `lem:perron` and Proposition `prop:constant`(a) (positive definite
`Sigma_beta`, real-analytic tilt), the paragraphs "Hypotheses (i) and (ii)" of the proof of
`thm:local` (for Lemma H only), `eq:A-radii` (`theta > 0`), Definition `def:tilt` and
Proposition `prop:rate` (identification of the rate and uniqueness of the tilt for real `z`). All
are proved in the paper for irreducible Metzler matrices, which `Q_G(z)` is for real `z >= 0`.

Overlap with the other route. The spectral route still needs a Gaussian integral with a complex
symmetric matrix (Lemma CL). That is unavoidable: for complex `z` the second-order term of
`-S J_G(beta,z)` is complex. What the route changes is the rest. There is no contour deformation:
Lemma R holds for every choice of radii, so the complex critical point is reached by choosing the
radii `theta(beta,z)` (Lemma T), not by moving a contour. The gap conditions come from (S1) to (S3),
a norm bound for a twisted stochastic matrix and the Perron gap, and the positive definite Hessian
at `z = 0` comes from `|nu| <= |u|` in (S4), without the computation of `app_torus.tex`.

## 10. Numerical check

Script `10_hypL_spectral_check.py`, output `10_hypL_spectral_output.txt`. Four non-reversible faces:

- (a) `F` = 4-cycle with rate 2 forward and 1 back, killing 0.3, `i = 3`, facet = path of three
  states (`g = 3`), `beta = (0.3, 0.3, 0.4)`.
- (b) `F` = complete graph on 4 states, rates in the script, `i = 3`, facet `K_3` (`g = 3`),
  `beta = (0.25, 0.35, 0.40)`.
- (c) `G` = 4-cycle with rate 2 forward and 1 back (`g = 4`), `i` entered from states 0, 2 and left
  to 1, 3, `beta = (0.2, 0.3, 0.25, 0.25)`.
- (d) `G` = complete graph on 4 states with random rates (seed 131), `g = 4`,
  `beta = (0.2, 0.3, 0.15, 0.35)`.

Values of `z`: `0`, `0.08`, `0.08i`, `-0.06 + 0.05i`, `0.1 e^{2.2 i}`. Start masses are positive at
`i`, so `mu^(z)` moves with `z`.

Part 1 (Lemma R). For all four faces, at `z = 0` and `z = 0.3 - 0.4i` (outside the small disc
on purpose, since Lemma R holds for every `z`), and for real radii and for complex radii, the
representation agrees with the word series of `lem:layer-exact` to a relative `5e-16` to `8e-14`
(face (d) at `z = 0.3 - 0.4i`: `4e-11`, the truncation of the word series at 13 letters per state).

Part 2 (tilt and Doob transform). Newton on the tilt equations converges to residual `< 1e-15` at
all five values of `z`. The rows of `P_0` sum to `1` to `1e-15`. At `z = 0` the matrix `P_0` of the
path (face (a)) has eigenvalues `1, 0, -1`, and that of the 4-cycle (face (c)) has `1, +-0.332i, -1`.
Both jump chains are periodic, and the eigenvalue `-1` stays for face (c) at every `z` (the added
jumps `j -> j'` go from `{0,2}` to `{1,3}` and keep the graph bipartite). The local law holds anyway
(Part 4), as (S3) says.

Part 3 (constants). `nu(0) = 1` to `1e-15` and `grad nu(0) = 0` to `2e-10` (finite differences) at
every `z`, including complex `z`. The ratio `det H_Phi / (det Theta^2 det Sigma / <theta,beta>^2)` is
`1` to `1.3e-6`, the finite-difference error, also at complex `z`. So `C_spectral = C_paper` to
about `1e-6` relative. The least eigenvalue of `Re H_Phi` is between `0.24` and `0.40`.

Part 4 (the local law). `eps = f^(z)(S beta) / (S^{-(g-1)/2} C e^{-S J}) - 1`, with the exact
value from Lemma R by the trapezoid rule on the torus (exponentially accurate for this periodic
analytic integrand; two grids agree to `1e-13` for `g = 3` and to `1e-7` or better for `g = 4`).
The value of `S |eps|` at `S = 25` and at the largest `S`:

| face | z = 0 | 0.08 | 0.08i | -0.06+0.05i | 0.1 e^{2.2i} |
|---|---|---|---|---|---|
| (a) path in 4-cycle, g = 3, S = 25 / 800 | 0.3003 / 0.2989 | 0.2481 / 0.2473 | 0.2870 / 0.2859 | 0.3790 / 0.3771 | 0.3519 / 0.3496 |
| (b) K3 in K4, g = 3, S = 25 / 800 | 0.2579 / 0.2568 | 0.2250 / 0.2242 | 0.2522 / 0.2512 | 0.2900 / 0.2884 | 0.2826 / 0.2812 |
| (c) G = 4-cycle, g = 4, S = 25 / 400 | 0.3311 / 0.3318 | 0.3203 / 0.3209 | 0.3305 / 0.3312 | 0.3400 / 0.3408 | 0.3394 / 0.3401 |
| (d) G = K4, g = 4, S = 25 / 400 | 0.2958 / 0.2957 | 0.2669 / 0.2668 | 0.2926 / 0.2925 | 0.3221 / 0.3219 | 0.3186 / 0.3184 |

So `|eps|` halves each time `S` doubles, and `S eps` tends to a finite complex constant, in every
case. This is the `O(1/S)` of Theorem L with the predicted `C_G(beta,z)` and `J_G(beta,z)`. The
radius check (real radii `theta(beta,0)` against the complex tilt, at `S = 100`) gives the same
value of `log f` to `1e-10` or better, which is Lemma R for complex radii at large `S`. These
numbers are checks. No step of the proof uses them.

## 11. Status

Proved. Hypothesis `hyp:L` holds for every `G` satisfying (H) with `|G| >= 2` and every compact
`K` in the open simplex on `G`, with `J_G(beta,z) = <d(z) - theta(beta,z), beta>` and `C_G(beta,z)`
as in Theorem L, by the spectral route: the exact torus representation of Lemma R (a matrix
exponential of the Fourier-twisted jump kernel), the complex tilt of Lemma T as radii, the Doob
transform of Lemma D, the spectral facts (S1) to (S4), and the cube Laplace lemma CL with a complex
Hessian. No aperiodicity condition and no irreducibility of `F` is needed. With it,
Theorem `thm:layer` becomes unconditional for all `k >= 2`. The constant `z_0` is not explicit.
Lemma H (identification of `C_G` with the paper's constant for real `z`) uses the computation in
the proof of `thm:local`, applied to `A(z)`.
