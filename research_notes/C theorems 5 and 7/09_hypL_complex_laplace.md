# Paper C, Hypothesis L: the local law of the weighted facet chain by a complex-phase Laplace lemma

Date October 24, 2026. Base checkpoint commit `0ffc041`. Write scope: this file and the files
`09_*` in this folder. No manuscript file was edited.

Inputs read, in this order. `kagey-problems/problem131/paperC/sec_boundary.tex` in full (the
setting of Section `sec:layer-setting`, Lemma `lem:layer-exact`, Hypothesis `hyp:L` at lines
366-376, the paragraph after it, Lemma `lem:L-two`, Theorem `thm:layer` and its proof, the
open-problems paragraph at lines 607-615). `app_torus.tex` (Lemma `lem:perron`, the proof of
Proposition `prop:constant`(a), Lemma `lem:torus` with its four steps, the proof of Theorem
`thm:local` with its paragraphs on hypotheses (i) to (iii), regularity and the constant).
`app_laplace.tex` (Lemma `lem:laplace` and Remark `rem:laplace-uniform`). For the definitions:
Definition `def:tilt` and Proposition `prop:constant` in `sec_secondorder.tex`, Proposition
`prop:rate` in `sec_dv.tex`, hypothesis (H) and Lemmas `lem:runs`, `lem:continuum` in
`sec_model.tex`. Then `research_notes/C theorems 5 and 7/08_T2_boundary_layer.md` (Section 6.1,
the outline of Lemma L, and Section 7), `research_notes/Paper C audits/04_boundary_layer_T2.md`
(Section 5, in particular 5.2 and 5.4), and item 3 under "Other mathematical concerns" in
`research_notes/Paper C audits/10_external_referee_report.md`. The scripts `08_layer_core.py` and
`paperC/verify_layer.py` were read for their routines (the Newton iteration for the tilt).

## The statement attacked

Hypothesis `hyp:L` of `sec_boundary.tex`, verbatim in the notation of the paper.

> Let `G` satisfy (H) with `|G| = k - 1 >= 2`, let `i` not in `G` with `F = G u {i}` irreducible,
> and let `Kc` be a compact subset of `Delta_G^o`. There are `z_0 > 0`, `C`, and functions
> `J_G(beta, z)` and `C_G(beta, z)` on `Kc x {|z| < 2 z_0}`, holomorphic in `z`, jointly
> continuous, real for real `z`, equal to the rate and the local-law constant of Section
> `sec:layer-setting` for real `0 <= z < 2 z_0`, and with `C_G(beta, 0) = C_G(beta) > 0`, such
> that uniformly for `beta` in `Kc`, `S >= 1` and complex `|z| <= z_0`
>
>     f^(z)_G(S beta) = S^{-(k-2)/2} C_G(beta, z) e^{-S J_G(beta, z)} (1 + eps),   |eps| <= C/S.

Here `f^(z)_G(s) = e^{-<d(z), s>} H_z(s)` with `H_z` the word sum of Lemma `lem:layer-exact`
(weights `mu^(z)`, `A(z)`, `e^(z)`), and `Q_G(z) = Q_G + z c^- (c^+)^T = A(z) - diag d(z)`.

The route followed is the one named in the open-problems paragraph and in item 3 of the external
report: the torus representation of Lemma `lem:torus` for complex weights by domination, the
holomorphic implicit function theorem for the complex critical point, the torus through that
point, and a Laplace lemma for a complex phase whose Hessian has positive definite real part,
with its constants written out. No other route was tried.

## 0. Summary

The route closes. Section 5 proves Hypothesis L for every `|G| >= 2` (Theorem 5.1), with the
constants uniform on `Kc x {|z| <= z_0}`. The four pieces are

- Lemma 2.1, the Gaussian integral for a complex symmetric matrix with positive definite real
  part (Hormander, Theorem 7.6.1), with the branch of the square root fixed;
- Lemma 2.2, the Laplace lemma of `app_laplace.tex` with a complex critical value and a complex
  symmetric Hessian `J` with `Re J >= sigma_min I`. The proof of Lemma `lem:laplace` goes through
  line by line with three changes: the factor `e^{T Psi(0)}` is complex and only its modulus is
  used, the Gaussian weight is bounded through `|e^{-x^T J x/2}| = e^{-x^T (Re J) x/2}`, and the
  Gaussian integral is Lemma 2.1;
- Lemma 3.1, the torus representation with complex weights and a general end vector, by the
  dominating nonnegative system `D(z) = A_G + |z| offdiag(c^- c^+T)`;
- Lemma 4.1, the complex critical point `zeta'(beta, z)` of the torus phase, with its uniform
  ball of existence and uniqueness (a contraction with parameters), its holomorphy in `z`, its
  conjugation symmetry, the Hessian `J(beta, z)`, and its identification with the tilt of `Q_G(z)`
  for real `z >= 0`.

The torus is then taken at the radii `|zeta'_j|` and rotated by `arg zeta'_j`. Lemma 3.1 holds at
these radii directly, so no separate contour-shift argument is needed; the "shift" is the fact
that the representation holds for every admissible radius vector. The hypotheses of Lemma 2.2
hold with constants that depend only on `Kc`, by continuity and compactness from the real case
`z = 0`, where the paper has already verified them.

The numerics (Section 7, `09_hypL_check.py`) compute the exact `f^(z)_G(S beta)` for two faces
with four states, a non-reversible 4-cycle and a non-reversible complete graph on four states, by a
word dynamic program, and compare with the prediction built from the complex tilt. The relative
error `eps` satisfies `S |eps| -> const` with consecutive ratios within `0.3` percent of `1` from
`S = 40` on, as `S` doubles from `5` to `160`, at nine `z` with `|z| <= 0.2` (eight of them
complex), so the error is `C/S` and not better. The word sum agrees with the 2-torus integral
through the complex critical point to `1e-15` where double precision allows, and the complex tilt
agrees with the torus critical point to machine precision. For the cycle the continued critical
point folds at `z = -0.070` on the negative real axis, which bounds the disc radius `z_0` of the
theorem for that chain, and the expansion still holds at `|z| = 0.2` in the other directions tested.

Status: proved. See the last line.

## 1. Notation and the facts taken from the paper

Throughout, `G = {1, ..., g}` with `g = k - 1 >= 2`, and `m = g - 1 = k - 2` is the number of
circles of the torus. State `1` of `G` is the one integrated out first. For `z` in `C`:

    A(z) = A_G + z offdiag(c^- c^+T),   entries a_jj'(z) = q_jj' + z c^-_j c^+_j'  (j != j'),
    d(z) = q_G - z c^- o c^+,   mu^(z) = mu_G + z mu_i c^+,   e^(z) = 1 + z c^-.

The dominating system is the nonnegative system at `|z|`:

    D(z) = A_G + |z| offdiag(c^- c^+T),   mu_D(z) = mu_G + |z| mu_i c^+,   e_D(z) = 1 + |z| c^-,

and `|A(z)| <= D(z)`, `|mu^(z)| <= mu_D(z)`, `|e^(z)| <= e_D(z)` entrywise. `D(z)` depends on `z`
only through `|z|`, is nondecreasing in `|z|`, and is irreducible since `A_G` is.

Split as in Appendix `app:torus`: `a_1(z) = (a_1j(z))_{j >= 2}`, `b_1(z) = (a_j1(z))_{j >= 2}`,
`A'(z) = (a_jj'(z))_{j, j' >= 2}`. For `z'` in `C^m` let `Z' = diag z'` and, where the inverse
exists,

    X_z(z') = (Z' - A'(z))^{-1},   g_z(z') = a_1(z)^T X_z(z') b_1(z),
    b_z(z') = (mu^(z)_1 + mu^(z)'^T X_z(z') b_1(z)) (e^(z)_1 + a_1(z)^T X_z(z') e^(z)').

The same letters with the subscript `D` denote these functions for the dominating system at real
radii `s'`. The torus phase is

    Phi_z(z') = beta_1 g_z(z') + sum_{j >= 2} beta_j z_j .

The word sum is `H_z(t) = sum_m W_z(m) prod_j t_j^{m_j - 1}/(m_j - 1)!` with `W_z` of Lemma
`lem:layer-exact`, and `f^(z)_G(s) = e^{-<d(z), s>} H_z(s)`.

Two standard facts, as in `app_torus.tex`: (first fact) for `B >= 0` and `S` diagonal positive,
`varrho(B - S) < 0` iff `varrho(S^{-1} B) < 1`, and then `(S - B)^{-1} = sum_n (S^{-1} B)^n S^{-1}
>= 0`; (second fact) a nonnegative eigenvector of an irreducible Metzler matrix is positive and
belongs to the Perron root. Here `varrho` of a Metzler matrix is its Perron root, the largest
real part of an eigenvalue, which is a continuous function of the entries. We also use: if `|B| <=
D` entrywise and `varrho(D) < 1`, then `sum_n |B^n| <= sum_n D^n` entrywise, so the Neumann series
of `B` converges absolutely.

Facts at `z = 0`, for the face `G` and the profile `beta` in `Delta_G^o`, from the paper.

- (F1) `theta(beta)`, the tilt of Definition `def:tilt` for `G`, is real-analytic and positive on
  `Delta_G^o` (Proposition `prop:constant`(a)), `varrho(A'_G - diag theta'(beta)) < 0`, and
  `g_0(theta'(beta)) = theta_1(beta)` (equation `eq:A-radii`).
- (F2) `grad_{z'} Phi_0(theta'(beta)) = 0`, and `H(beta) = grad^2_{z'} Phi_0(theta'(beta)) =
  B^T Sigma_beta B` with `B = I + 1 beta'^T / beta_1` is real symmetric positive definite, with
  `det H(beta) = det Sigma_beta / beta_1^2` (proof of Theorem `thm:local`, hypotheses (i) and
  (ii)). `H(beta)` is continuous in `beta`, since `Sigma_beta` is real-analytic.
- (F3) `Re Phi_0(theta' e^{i phi}) <= Phi_0(theta') - sum_{j >= 2} beta_j theta_j (1 - cos phi_j)`
  for `phi` in `T^m` (proof of Theorem `thm:local`, hypothesis (iii)).
- (F4) `b_0(theta'(beta)) = (mu_G . r_beta)(l_beta . 1)/beta_1 > 0` under (H) (paragraph "The
  constant" of that proof).
- (F5) `J_G(beta) = <q_G - theta(beta), beta>` and `C_G(beta) = (2 pi)^{-m/2} det(Theta' H Theta')^{-1/2}
  b_0(theta') prod_{j >= 2} theta_j` with `Theta' = diag theta'`, which is Definition `def:tilt`.
- (F6) For real `z >= 0` the matrix `Q_G(z)` is Metzler and irreducible and `A(z) >= 0`. Facts
  (F1), (F2), (F4), (F5) hold for `A(z)`, `mu^(z)`, `e^(z)` in place of `A_G`, `mu_G`, `1`, with the
  tilt `theta(beta, z)` of `Q_G(z)` at `beta`, the rate `J_G(beta, z) = <d(z) - theta(beta, z), beta>`
  and the constant `C_G(beta, z)` of Section `sec:layer-setting`. The derivations in the paper use
  only that the off-diagonal matrix is nonnegative and irreducible and that `theta(beta, z)` is a
  point of `V` for it (Lemma `lem:perron`, the first and second facts), and `b_z(theta') =
  (mu^(z) . r)(l . e^(z))/beta_1` follows from `r' = r_1 X b_1`, `l' = l_1 X^T a_1`, `l_1 r_1 =
  beta_1` exactly as for `e = 1`. Also `theta(beta, z)` is jointly continuous in `(beta, z)` on
  `Delta_G^o x [0, z_1)` for some `z_1 > 0` (Proposition `prop:layer-constants`(ii): the critical
  point `psi(z)` is real-analytic in `(beta, z)` near `(beta, 0)`, and for real `z >= 0` it is the
  maximizer of a function that is strictly concave modulo constants, so `theta(beta, z) =
  A(z) e^psi / e^psi` with this `psi`).

## 2. The Laplace lemma with a complex phase

**Lemma 2.1 (Gaussian integral, complex symmetric matrix).** Let `S_m^+` be the set of complex
symmetric `m x m` matrices `J` with `Re J` positive definite. Then `S_m^+` is convex, `det J != 0`
on it, and there is exactly one continuous function `J -> det(J)^{-1/2}` on `S_m^+` whose square is
`1/det J` and which is positive for real `J`. With this branch, for every `J` in `S_m^+`,

    int_{R^m} e^{-x^T J x / 2} dx = (2 pi)^{m/2} det(J)^{-1/2}.

*Proof.* Convexity is clear. If `J x = 0` with `x != 0`, then `0 = Re(x^* J x) = x^* (Re J) x > 0`,
since `x^* (Re J) x` and `x^* (Im J) x` are real for real symmetric `Re J`, `Im J`. So `det J != 0`.
A convex set is simply connected, so `1/det J` has exactly two continuous square roots on `S_m^+`,
and the real positive definite matrices form a connected subset on which one of them is positive.
Both sides are holomorphic functions of the entries `(J_jk)_{j <= k}` on the open set `S_m^+` in
`C^{m(m+1)/2}`: the left side because `|e^{-x^T J x/2}| = e^{-x^T (Re J) x/2} <= e^{-sigma |x|^2/2}`
locally uniformly in `J`, which allows differentiation under the integral; the right side because
a continuous square root of a nonvanishing holomorphic function is holomorphic. They agree on the
real positive definite matrices, the classical Gaussian integral. A holomorphic function on a
connected open subset of `C^n` that vanishes on a nonempty open subset of `R^n` vanishes
identically, since its Taylor coefficients at a real point are determined by derivatives in real
directions. This is Theorem 7.6.1 of Hormander, The Analysis of Linear Partial Differential
Operators I, where the branch is described in the same way. ∎

**Lemma 2.2 (Laplace integrals with a complex phase, uniform form).** Let `P` be a set and
`m >= 1`. Let `Psi, a : P x T^m -> C` be such that the `phi`-derivatives of `Psi` up to order 4 and
of `a` up to order 2 exist, are continuous in `phi`, and are bounded in modulus by `B_Psi` and `B_a`
on `P x T^m`. Let `sigma_min > 0`, `eta > 0` and `epsilon` in `(0, 1)` with
`m^3 B_Psi epsilon <= (3/2) sigma_min`. Assume that for every `p` in `P`

- (i) `grad_phi Psi(p, 0) = 0`;
- (ii) `J(p) = -grad^2_phi Psi(p, 0)`, which is complex symmetric, satisfies `Re J(p) >= sigma_min I`;
- (iii) `Re Psi(p, phi) - Re Psi(p, 0) <= -eta` for every `phi` in `T^m` with `||phi|| >= epsilon`.

Then, uniformly for `p` in `P` and `T >= 1`,

    int_{T^m} e^{T Psi(p, phi)} a(p, phi) dphi
        = e^{T Psi(p, 0)} (2 pi / T)^{m/2} det J(p)^{-1/2} ( a(p, 0) + O(1/T) ),

with the branch of Lemma 2.1, and with a constant in `O` that depends only on `m`, `B_Psi`, `B_a`,
`sigma_min`, `epsilon` and `eta`.

Hypothesis (i) of Lemma `lem:laplace`, that `Psi(p, 0)` is real, is dropped, and hypothesis (ii),
that `J` is real positive definite, is weakened to `Re J >= sigma_min I`. The proof is that of
Lemma `lem:laplace` with Remark `rem:laplace-uniform`. We write it out so that each line can be
checked against the real case.

*Proof.* Below `C` depends only on `m`, `sigma_min`, `B_Psi`, `B_a`, `epsilon`, `eta`, and it may
change from line to line. Write `Psi_0 = Psi(p, 0)`, so `|e^{T Psi_0}| = e^{T Re Psi_0}`.

*Localization.* On `||phi|| >= epsilon`, by (iii), `|e^{T Psi} a| <= B_a e^{T (Re Psi_0 - eta)}`. So the
integral over this set has modulus at most `(2 pi)^m B_a e^{-eta T} |e^{T Psi_0}| <= C T^{-1-m/2}
|e^{T Psi_0}|`, since `e^{-eta T} <= C_eta T^{-1-m/2}` for `T >= 1`.

*Scaling.* Reduction modulo `2 pi` identifies the cube `||x|| <= epsilon` of `R^m` with the set
`||phi|| <= epsilon`, and preserves the measure. Put `R(phi) = Psi(p, phi) - Psi_0 + (1/2) phi^T J phi`,
a complex-valued function. By (i) and (ii), `R` and its derivatives of orders 1 and 2 vanish at
`phi = 0`. Taylor's theorem with integral remainder, valid for complex-valued functions, gives on
the cube `R = (1/6) Psi_ijk phi^i phi^j phi^k + omega_0` with `|omega_0| <= C ||phi||^4`, where
`Psi_ijk` are the third derivatives at `(p, 0)`, and also `|R| <= (m^3/6) B_Psi ||phi||^3`, since
`sum_{|gamma| = 3} 1/gamma! = m^3/6`. As `||phi||^3 <= epsilon |phi|^2` on the cube and
`m^3 B_Psi epsilon <= (3/2) sigma_min`, this gives `|R| <= (1/4) sigma_min |phi|^2`. Substitute
`phi = x / sqrt T` and put `w(x) = T R(x / sqrt T)`. The integral over the cube is

    T^{-m/2} e^{T Psi_0} int_{||x|| <= epsilon sqrt T} e^{-x^T J x/2} e^{w(x)} a(p, x/sqrt T) dx,

and `|w(x)| <= (1/4) sigma_min |x|^2`.

*Taylor expansion.* Let `P(x) = (1/6) Psi_ijk x^i x^j x^k`, `a_0 = a(p, 0)`, `a_i = d a / d phi_i (p, 0)`.
Then `w = T^{-1/2} P + omega_1` with `|omega_1| <= C T^{-1} |x|^4`, and `|w| <= C T^{-1/2} |x|^3`.
From `|e^w - 1 - w| <= (1/2)|w|^2 e^{|w|}` we get `|e^w - 1 - T^{-1/2} P| <= C T^{-1}(|x|^4 + |x|^6)
e^{sigma_min |x|^2/4}`. Taylor's theorem for `a` gives `|a(p, x/sqrt T) - a_0| <= C T^{-1/2} |x|` and
`|a(p, x/sqrt T) - a_0 - T^{-1/2} a_i x^i| <= C T^{-1} |x|^2`. Multiplying out,

    e^w a(p, x/sqrt T) = a_0 + T^{-1/2} (a_0 P(x) + a_i x^i) + omega(x),
    |omega(x)| <= C T^{-1} (1 + |x|)^6 e^{sigma_min |x|^2/4}.

*Integration.* Here is the one place where the complex Hessian enters: `|e^{-x^T J x/2}| =
e^{-x^T (Re J) x/2} <= e^{-sigma_min |x|^2/2}` by (ii). So `omega` contributes at most
`C T^{-1} int (1 + |x|)^6 e^{-sigma_min |x|^2/4} dx = C T^{-1}`. Outside the cube `|x| > epsilon sqrt T`,
so extending the integrals of the other two terms to `R^m` changes them by at most
`C e^{-sigma_min epsilon^2 T/4} <= C T^{-1}`. On `R^m`, `int e^{-x^T J x/2} dx = (2 pi)^{m/2} det J^{-1/2}`
by Lemma 2.1, and the odd polynomial `a_0 P(x) + a_i x^i` integrates to `0` against the even weight
`e^{-x^T J x/2}`, which is absolutely integrable. So the integral over the cube is
`e^{T Psi_0} T^{-m/2} [ (2 pi)^{m/2} det J^{-1/2} a_0 + O(T^{-1}) ]`. By Hadamard's inequality
`|det J| <= (m B_Psi)^m`, so `|det J^{-1/2}| >= (m B_Psi)^{-m/2}`, and this error and the one from the
localization are `O(1/T)` relative to `e^{T Psi_0} (2 pi/T)^{m/2} det J^{-1/2}`. ∎

## 3. The torus representation with complex weights

**Lemma 3.1 (torus representation, complex weights, general end vector).** Let `z` in `C` and
`s'` in `(0, inf)^m` satisfy `varrho(D'(z) - diag s') < 0`. Then on the set of `z'` in `C^m` with
`|z_j| >= s_j` for every `j >= 2`, the matrix `Z' - A'(z)` is invertible, and `X_z`, `g_z`, `b_z` are
given by absolutely convergent series in `1/z_2, ..., 1/z_g` whose terms are dominated in modulus
by the corresponding terms of the series of the dominating system at `s'`. Hence

    |g_z(z')| <= g_D(s'),   |b_z(z')| <= b_D(s')   for |z_j| >= s_j.

The functions `g_z(z')` and `b_z(z')` are holomorphic in `(z, z')` on the open set where
`Z' - A'(z)` is invertible, which contains `{(z, z') : varrho(D'(z) - diag |z'|) < 0}`. For every
`t` in `(0, inf)^G`,

    H_z(t) = (2 pi)^{-m} int_{T^m} exp( t_1 g_z(z') + sum_{j >= 2} t_j z_j ) b_z(z') prod_{j >= 2} z_j dphi,
    z_j = s_j e^{i phi_j}.

*Proof.* The four steps of Lemma `lem:torus`, with the dominating system in the places where
nonnegativity was used.

*Step 1.* By the first fact, `varrho(diag(s')^{-1} D'(z)) < 1`. For `|z_j| >= s_j` the entries of
`Z'^{-1} A'(z)` are dominated in modulus by those of `diag(s')^{-1} D'(z)`, so the Neumann series
`X_z(z') = sum_n (Z'^{-1} A'(z))^n Z'^{-1}` converges absolutely, its terms being dominated by those
of `X_D(s') = (diag s' - D'(z))^{-1} >= 0`. So `Z' - A'(z)` is invertible, and the series for
`g_z = a_1(z)^T X_z b_1(z)` and for the two factors of `b_z` are dominated termwise by the series
of `g_D(s')` and of the factors of `b_D(s')`, because `|a_1(z)| <= a_{1,D}`, `|b_1(z)| <= b_{1,D}`,
`|mu^(z)| <= mu_D`, `|e^(z)| <= e_D` entrywise. This gives the two bounds. Where `Z' - A'(z)` is
invertible, its inverse is holomorphic in `(z, z')` by Cramer's rule, so `g_z(z')` and `b_z(z')`
are holomorphic there.

*Step 2.* Choose `s_1 > g_D(s')` and put `S = diag(s_1, s')`. As in Step 2 of Lemma `lem:torus`,
with `D(z)` in place of `A_F`, `varrho(S^{-1} D(z)) < 1`.

*Step 3.* Let `Z = diag(z)` with `|z_j| = s_j` for all `j` in `G`. The entries of `A(z) Z^{-1}` are
dominated in modulus by those of `D(z) S^{-1}`, which has spectral radius `varrho(S^{-1} D(z)) < 1`
(the two matrices are similar). So

    mu^(z)T (Z - A(z))^{-1} e^(z) = sum_c mu^(z)_{c_1} prod_{l < M} a_{c_l c_{l+1}}(z) e^(z)_{c_M} prod_{j in G} z_j^{-m_j(c)},

the sum over the words `c = c_1 ... c_M` in `G` with `M >= 1` and `c_l != c_{l+1}`, absolutely and
uniformly on the torus, by the Neumann series `(Z - A(z))^{-1} = Z^{-1} sum_n (A(z) Z^{-1})^n`.
Multiply by `e^{<t, z>} prod_j z_j` and integrate term by term. Cauchy's formula
`(2 pi)^{-1} int_0^{2 pi} e^{t_j z_j} z_j^{1 - n} dphi_j = t_j^{n-1}/(n-1)!` for `n >= 1` and `0` for
`n <= 0` kills the words that miss a state, and grouping the others by `m(c)` gives
`H_z(t) = (2 pi)^{-g} int_{T^g} e^{<t, z>} mu^(z)T (Z - A(z))^{-1} e^(z) prod_j z_j dphi`, which is
the word sum with the weights `mu^(z)`, `A(z)`, `e^(z)` of Lemma `lem:layer-exact`.

*Step 4.* Block inversion with the Schur complement `z_1 - g_z(z')` of `Z' - A'(z)` in `Z - A(z)`,
which is nonzero since `|g_z(z')| <= g_D(s') < s_1`, gives

    mu^(z)T (Z - A(z))^{-1} e^(z) = b_z(z') / (z_1 - g_z(z')) + mu^(z)'^T X_z(z') e^(z)' .

This is the identity of the paper with the general end vector: the `(1,1)`, `(1,2)`, `(2,1)` and
`(2,2)` blocks of the inverse are `1/(z_1 - g)`, `a_1^T X/(z_1 - g)`, `X b_1/(z_1 - g)` and
`X + X b_1 a_1^T X/(z_1 - g)`, and `mu^T (.) e` collects into the product of the two factors of
`b_z` over `z_1 - g_z`, plus `mu'^T X e'`. The second term does not depend on `z_1` and gives
`(2 pi)^{-1} int e^{t_1 z_1} z_1 dphi_1 = 0`. In the first term `g_z(z')` lies inside the circle
`|z_1| = s_1`, so Cauchy's formula gives `e^{t_1 g_z(z')} b_z(z')`. ∎

## 4. The complex critical point

**Lemma 4.1 (the complex critical point).** Let `Kc` be a compact subset of `Delta_G^o`. There are
`z_1 > 0`, `r_0 > 0`, `c_0 > 0`, `sigma_0 > 0` and `B < inf`, depending only on `Kc`, `Q` and `mu`,
such that the following hold.

- (a) For `beta` in `Kc`, `|z| <= z_1` and real `s'` with `||s' - theta'(beta)|| <= 3 r_0`:
  `s' > 0` and `varrho(D'(z) - diag s') <= -c_0`. Also `r_0 < (1/4) min_{Kc} min_j theta_j(beta)`.
- (b) `g_z(z')` and `b_z(z')` are holomorphic in `(z, z')` on `{|z| < z_1} x U_beta`, where
  `U_beta = {z' : |z_j| > theta_j(beta) - 3 r_0 for all j >= 2}`. On `{|z| <= z_1} x Bbar(theta'(beta), r_0)`
  their derivatives in `(z, z')` up to order `6` are bounded in modulus by `B`, uniformly in
  `beta` in `Kc`.
- (c) For `beta` in `Kc` and `|z| < z_1` there is exactly one `zeta'(beta, z)` in
  `Bbar(theta'(beta), r_0)` with `grad_{z'} Phi_z(zeta'(beta, z)) = 0`. It is holomorphic in `z` on
  `|z| < z_1`, jointly continuous in `(beta, z)`, satisfies `zeta'(beta, 0) = theta'(beta)`,
  `||zeta'(beta, z) - theta'(beta)|| <= B |z|`, and `zeta'(beta, zbar) = conj zeta'(beta, z)`.
- (d) Put `Z_c = diag zeta'(beta, z)` and `J(beta, z) = Z_c grad^2_{z'} Phi_z(zeta'(beta, z)) Z_c`.
  Then `J(beta, z)` is complex symmetric, jointly continuous, `J(beta, 0) = Theta' H(beta) Theta'`
  is real symmetric, and `J(beta, 0) >= sigma_0 I`. Moreover, for `Psi(beta, z, phi) =
  Phi_z(zeta'(beta, z) e^{i phi})` (entrywise product), `grad_phi Psi(beta, z, 0) = 0` and
  `-grad^2_phi Psi(beta, z, 0) = J(beta, z)`.
- (e) For real `z` in `[0, z_1)`: `zeta'(beta, z) = theta'(beta, z)`, the tilt of `Q_G(z)` at `beta`
  without its first entry; `Phi_z(zeta'(beta, z)) = <beta, theta(beta, z)>`; `J(beta, z) =
  Theta'(beta, z) H(beta, z) Theta'(beta, z)` is real positive definite with
  `det J(beta, z) = prod_{j >= 2} theta_j(beta, z)^2 det Sigma_beta(z)/beta_1^2`; and
  `b_z(zeta'(beta, z)) = (mu^(z) . r_beta(z))(l_beta(z) . e^(z))/beta_1 > 0`.

*Proof.* (a) The map `(beta, z, s') -> varrho(D'(z) - diag s')` is continuous. At `(beta, 0,
theta'(beta))` it is negative by (F1), and `theta'` is continuous and positive on the compact set
`Kc`. So there are `r_0 < (1/4) min_{Kc} min_j theta_j` and `z_1 > 0` with the claim, by uniform
continuity on a compact neighborhood of `{(beta, 0, theta'(beta)) : beta in Kc}`.

(b) Put `s'_beta = theta'(beta) - 3 r_0 1 > 0`. By (a), `varrho(D'(z) - diag s'_beta) < 0` for
`|z| <= z_1`. For `z'` in `U_beta` we have `|z_j| > s_{beta, j}`, so by Lemma 3.1 the matrix
`Z' - A'(z)` is invertible on the open set `{|z| < z_1} x U_beta`, and `g_z`, `b_z` are holomorphic
there, with `|g_z(z')| <= g_D(s'_beta)` and `|b_z(z')| <= b_D(s'_beta)`, where `D = D(z)`. As
`D(z)` is nondecreasing in `|z|` and the Neumann series are monotone, these are at most
`g_{D(z_1)}(s'_beta)` and `b_{D(z_1)}(s'_beta)`, which are continuous in `beta` and hence bounded
on `Kc`. A polydisc of radius `min(z_1/2, r_0)` around a point of `{|z| <= z_1/2} x Bbar(theta'(beta), r_0)`
lies in `{|z| < z_1} x {|z_j| > theta_j - 2 r_0}`, inside the open set. Cauchy's estimates there
bound the derivatives up to order `6` by the sup bound times `6!/min(z_1/2, r_0)^6`. We replace
`z_1` by `z_1/2` and call it `z_1` again.

(c) Let `F(beta, z, z') = grad_{z'} Phi_z(z') = beta_1 grad g_z(z') + beta'`, holomorphic in `(z, z')`
and continuous in `beta`. By (F2), `F(beta, 0, theta'(beta)) = 0` and `D_{z'} F(beta, 0, theta'(beta))
= H(beta)` is invertible, with `||H(beta)^{-1}|| <= B_1` on `Kc` by continuity and compactness. Put
`T_{beta, z}(z') = z' - H(beta)^{-1} F(beta, z, z')`. By (b), `D_{z'} F` is Lipschitz in `(z, z')` on
`{|z| <= z_1} x Bbar(theta', r_0)` with a constant `B_2`, and `F(beta, ., theta')` is Lipschitz in
`z` with a constant `B_3`, both uniform in `beta`. Hence on `Bbar(theta', r)`, for `r <= r_0`,

    ||D_{z'} T_{beta, z}|| = ||H^{-1} (D_{z'} F(beta, 0, theta') - D_{z'} F(beta, z, z'))|| <= B_1 B_2 (|z| + r),
    ||T_{beta, z}(theta') - theta'|| = ||H^{-1} (F(beta, z, theta') - F(beta, 0, theta'))|| <= B_1 B_3 |z|.

Choose `r <= r_0` and `z_2 <= z_1` with `B_1 B_2 (z_2 + r) <= 1/2` and `B_1 B_3 z_2 <= r/2`. Then
for `|z| <= z_2`, `T_{beta, z}` maps `Bbar(theta', r)` into itself (since `||T(z') - theta'|| <=
||T(z') - T(theta')|| + ||T(theta') - theta'|| <= r/2 + r/2`) and is a contraction with constant
`1/2`. Its unique fixed point `zeta'(beta, z)` is the unique zero of `F(beta, z, .)` in the ball,
and `||zeta' - theta'|| <= 2 ||T(theta') - theta'|| <= 2 B_1 B_3 |z|`. The iterates `T^n(theta')`
are holomorphic in `z` on `|z| < z_2` and continuous in `(beta, z)`, and they converge uniformly
at a geometric rate, so `zeta'` is holomorphic in `z` and continuous in `(beta, z)`. At `z = 0`
the fixed point is `theta'(beta)`. All the data `A_G`, `c^-`, `c^+`, `beta` are real, so
`F(beta, zbar, conj z') = conj F(beta, z, z')`; hence `conj zeta'(beta, z)` is a zero of
`F(beta, zbar, .)` in the ball and equals `zeta'(beta, zbar)` by uniqueness. We rename `z_2`, `r`
as `z_1`, `r_0`.

(d) `grad^2 Phi_z` is symmetric and `Z_c` is diagonal, so `J` is complex symmetric; it is
continuous by (b) and (c). At `z = 0`, `Z_c = Theta'` and `grad^2 Phi_0(theta') = H(beta)`, so
`J(beta, 0) = Theta' H(beta) Theta'`, real positive definite, continuous in `beta`, hence
`>= sigma_0 I` on `Kc` for some `sigma_0 > 0`. For the `phi`-derivatives, with `w_j = zeta_j e^{i phi_j}`,
`d Psi / d phi_j = i w_j d_j Phi_z(w)` and
`d^2 Psi / d phi_k d phi_j = (i w_j)(i w_k) d_{jk} Phi_z(w) + delta_{jk} (i)^2 w_j d_j Phi_z(w)`.
At `phi = 0` the first derivatives vanish by (c), and the second derivatives are
`-zeta_j zeta_k d_{jk} Phi_z(zeta') - delta_{jk} zeta_j d_j Phi_z(zeta')`, whose last term is `0`.

(e) Let `z` be real in `[0, z_1)`. Then `A(z) >= 0` is irreducible and `theta(beta, z)` is the
tilt of `Q_G(z)` at `beta` (Proposition `prop:rate`(b) for `Q_G(z)`). By (F6), `theta(beta, z)` is
jointly continuous on `Kc x [0, z_1)`, so after shrinking `z_1`, `||theta'(beta, z) - theta'(beta)||
<= r_0` on `Kc`. By (F1) and (F2) for `A(z)`, `theta'(beta, z)` is a zero of `F(beta, z, .)`: for
real `z'` near `theta'(beta, z)` the vector `(1, X_z(z') b_1(z)) >= 0` lies in the kernel of
`A(z) - diag(g_z(z'), z')`, so by the second fact `lambda(g_z(z'), z') = 0` for the Perron root
`lambda(y) = varrho(A(z) - diag y)`, and differentiating at `theta'(beta, z)` with
`grad lambda(theta(beta, z)) = -beta` (Lemma `lem:perron`) gives `d_j g_z = -beta_j/beta_1`. By
uniqueness in (c), `zeta'(beta, z) = theta'(beta, z)`. Then `Phi_z(zeta') = beta_1 g_z(theta') +
sum_{j >= 2} beta_j theta_j = <beta, theta(beta, z)>` by `g_z(theta') = theta_1`, and the
statements on `J` and `b_z` are (F2), (F4), (F5) for `A(z)`, `mu^(z)`, `e^(z)`. ∎

## 5. Hypothesis L

**Theorem 5.1 (Hypothesis L).** Let `G` satisfy (H) with `|G| = k - 1 >= 2`, let `i` not in `G`, and
let `Kc` be a compact subset of `Delta_G^o`. Then Hypothesis `hyp:L` holds for `G`, `i` and `Kc`,
with

    J_G(beta, z) = <d(z), beta> - Phi_z(zeta'(beta, z)),
    C_G(beta, z) = (2 pi)^{-(k-2)/2} det J(beta, z)^{-1/2} b_z(zeta'(beta, z)) prod_{j >= 2} zeta_j(beta, z),

where `zeta'` and `J` are those of Lemma 4.1, and the branch of `det J^{-1/2}` is that of Lemma 2.1.

The irreducibility of `F = G u {i}` is not used. It only guarantees that `c^-` and `c^+` are
nonzero, so that `z` enters at all.

*Proof.* Let `m = k - 2`, and let `z_1`, `r_0`, `sigma_0`, `B` be as in Lemma 4.1. Write
`zeta' = zeta'(beta, z)`, `rho_j = |zeta_j|`, and `phi^c_j = Arg zeta_j`. Put
`Psi(beta, z, phi) = Phi_z(zeta' e^{i phi})` and `chi(beta, z, phi) = b_z(zeta' e^{i phi}) prod_{j >= 2} zeta_j e^{i phi_j}`.

*Step 1, the choice of `z_0`.* Let `P_1 = Kc x {|z| <= z_1/2}`. For `(beta, z)` in `P_1` and `phi`
in `T^m`, `|zeta_j e^{i phi_j}| = rho_j` and `|rho_j - theta_j(beta)| <= |zeta_j - theta_j(beta)| <= B |z|`.
Shrink `z_1` so that `B z_1 <= r_0`. Then `rho_j >= theta_j - r_0 > theta_j - 3 r_0`, so the points
`(z, zeta' e^{i phi})` lie in the open set of Lemma 4.1(b), and `Psi`, `chi` are smooth in `phi`
with all `phi`-derivatives jointly continuous on the compact set `P_1 x T^m` (chain rule, with
`zeta'` continuous). Let `B_Psi`, `B_a` be bounds for the derivatives of `Psi` up to order 4 and
of `chi` up to order 2 there. Also `Re zeta_j > 0`, since `r_0 < theta_j/4`, so `phi^c_j` in
`(-pi/2, pi/2)` is continuous. Now choose `z_0 <= z_1/4` so that for `|z| <= 2 z_0` and `beta` in
`Kc`:

- (alpha) `||rho' - theta'(beta)|| <= r_0`, which holds already;
- (beta) `Re J(beta, z) >= (sigma_0/2) I`. This follows from `||J(beta, z) - J(beta, 0)|| <= sigma_0/2`
  for `|z| <= 2 z_0`, by uniform continuity of `J` on `P_1`, since `Re J = J(beta, 0) + Re(J - J(beta, 0))`
  and `||Re M|| <= ||M||`;
- (gamma) `|chi(beta, z, 0)| >= c_chi > 0`. At `z = 0`, `chi(beta, 0, 0) = b_0(theta') prod_j theta_j
  > 0` by (F4), continuous on `Kc`, hence `>= 2 c_chi`; uniform continuity gives `>= c_chi`;
- (delta) the gap. Fix `epsilon` in `(0, 1)` with `m^3 B_Psi epsilon <= (3/2)(sigma_0/2)`. By (F3),
  `Re Psi(beta, 0, phi) - Psi(beta, 0, 0) <= -beta_min theta_min (1 - cos epsilon) =: -2 eta` for
  `||phi|| >= epsilon`, where `beta_min = min_{Kc} min_j beta_j > 0` and `theta_min = min_{Kc} min_j
  theta_j > 0`. The function `(beta, z, phi) -> Re[Psi(beta, z, phi) - Psi(beta, z, 0)]` is
  uniformly continuous on `P_1 x T^m`, so for `|z| <= 2 z_0` it differs from its value at `z = 0`
  by at most `eta`, and `Re Psi(beta, z, phi) - Re Psi(beta, z, 0) <= -eta` for `||phi|| >= epsilon`.

*Step 2, the representation.* Let `beta` in `Kc`, `|z| <= z_0`, `S >= 1`. By (alpha) and Lemma
4.1(a), the radii `s' = rho'` are admissible, so Lemma 3.1 with `t = S beta` gives

    H_z(S beta) = (2 pi)^{-m} int_{T^m} exp( S [beta_1 g_z(rho' e^{i phi'}) + sum_j beta_j rho_j e^{i phi'_j}] )
                      b_z(rho' e^{i phi'}) prod_j rho_j e^{i phi'_j} dphi'.

The translation `phi' = phi + phi^c` of `T^m` preserves the measure and turns
`rho_j e^{i phi'_j}` into `zeta_j e^{i phi_j}`. So

    H_z(S beta) = (2 pi)^{-m} int_{T^m} e^{S Psi(beta, z, phi)} chi(beta, z, phi) dphi.

This is the torus through the complex critical point. Nothing was shifted: Lemma 3.1 holds at
every admissible radius vector, and the integrand is holomorphic in `z'` on the product of annuli
between `theta'(beta)` and `rho'`, which is the reason the two representations agree.

*Step 3, the Laplace lemma.* On `P_0 = Kc x {|z| <= z_0}` the hypotheses of Lemma 2.2 hold:
(i) and the form of `J` by Lemma 4.1(c), (d); (ii) with `sigma_min = sigma_0/2` by (beta); (iii)
by (delta); the bounds `B_Psi`, `B_a` by Step 1. Hence, uniformly on `P_0` and for `S >= 1`,

    int e^{S Psi} chi dphi = e^{S Psi(beta, z, 0)} (2 pi/S)^{m/2} det J(beta, z)^{-1/2} ( chi(beta, z, 0) + O(1/S) ).

Since `f^(z)_G(S beta) = e^{-S <d(z), beta>} H_z(S beta)` and `Psi(beta, z, 0) = Phi_z(zeta')`,

    f^(z)_G(S beta) = S^{-m/2} C_G(beta, z) e^{-S J_G(beta, z)} (1 + eps),   eps = O(1/S)/chi(beta, z, 0),

and `|eps| <= C/S` by (gamma), with `C` depending only on `Kc`, `Q`, `mu`.

*Step 4, the properties of `J_G` and `C_G`.* Define them on `Kc x {|z| < 2 z_0}` by the displayed
formulas; (beta) and (gamma) hold there. `zeta'(beta, z)` is holomorphic in `z` and
`(z, z') -> g_z(z'), b_z(z')` are holomorphic, so `Phi_z(zeta')`, `b_z(zeta')`, `prod zeta_j` and
`det J(beta, z)` are holomorphic in `z`; `d(z)` is affine. So `J_G` is holomorphic in `z`. By
(beta), `J(beta, z)` lies in `S_m^+`, so `det J != 0`, and `(beta, z) -> det J(beta, z)^{-1/2}` is
continuous as the composition of a continuous map into `S_m^+` with the continuous branch of
Lemma 2.1; a continuous square root of a nonvanishing holomorphic function of `z` is holomorphic.
So `C_G` is holomorphic in `z`, and both are jointly continuous. Real for real `z`: by Lemma 4.1(c),
`zeta'(beta, z)` is real for real `z`, so `Phi_z(zeta')`, `J(beta, z)` and `b_z(zeta')` are real,
`J(beta, z)` is real symmetric with `Re J = J > 0`, `det J > 0`, and the branch of Lemma 2.1 is the
positive root. Equality with the rate and the constant for real `0 <= z < 2 z_0`: by Lemma 4.1(e),
`J_G(beta, z) = <d(z) - theta(beta, z), beta>`, which is the rate of `Q_G(z)` at `beta` (Definition
`def:tilt`, `J = <q - theta, alpha>`, applied to `Q_G(z)`, whose diagonal is `-d(z)`), and
`det J(beta, z) = prod theta_j^2 det Sigma_beta(z)/beta_1^2` together with
`b_z(theta') prod theta_j = (mu^(z) . r)(l . e^(z)) prod theta_j/beta_1` gives
`C_G(beta, z) = (mu^(z) . r_beta(z))(l_beta(z) . e^(z)) / ((2 pi)^{m/2} sqrt(det Sigma_beta(z)))`,
the constant of Section `sec:layer-setting`. At `z = 0` this is `C_G(beta) > 0` by (H). ∎

**Remark 5.2 (what the proof uses).** The proof uses (H) for `G` twice: irreducibility for (F1)
to (F3) and for the Perron facts, and `mu(G) > 0` for (F4), which is the lower bound (gamma). It
uses `|G| >= 2` so that the torus has at least one circle, and the compactness of `Kc` for every
constant. These are the hypotheses of `hyp:L`. In Theorem `thm:layer` the facet `G` is assumed to
satisfy (H), so the theorem becomes unconditional for every `k >= 2`.

**Remark 5.3 (the role of small `z_0`).** The only place where `|z|` must be small is Step 1: the
real part of the Hessian, the lower bound on the amplitude, and the gap are inherited from `z = 0`
by continuity. For larger `|z|` two things can go wrong: the real part of `J(beta, z)` can fail to
be positive definite, and the continued critical point can reach a fold, where its Hessian is
singular and it ceases to exist. On the negative real axis `-z P_beta` is convex, so for `z < 0`
the critical point is a saddle of `Psi_beta - z P_beta`, and Section 7 finds such a fold at
`z = -0.070` for the 4-cycle at `beta = (0.5, 0.3, 0.2)`. So `z_0` can be small, and the region of
validity is not a disc. Theorem `thm:layer` needs only `z_* <= z_0/2`, which it gets by taking
`delta` small, so this is no loss.

**Remark 5.4 (relation to Hormander 7.7.5).** Lemma 2.2 is the special case of the stationary
phase theorem with an analytic phase in which the critical point has already been moved onto the
contour. We did not use Theorem 7.7.5 because its constants are stated for a fixed phase, and the
uniformity over `(beta, z)` is the whole point; the proof of Lemma `lem:laplace` already carries
the constants, and only the Gaussian step changes.

## 6. Hypotheses on the face, checked against the paper

| Needed | Where used | Standing assumption that supplies it |
|---|---|---|
| `G` irreducible, `g >= 2` | (F1) to (F3), Lemma 3.1 Step 2, Lemma 4.1(a), (e) | (H) for `G` in `hyp:L` and `thm:layer` |
| `mu(G) > 0` | (F4), lower bound (gamma) | (H) for `G` |
| `Kc` compact in `Delta_G^o` | every constant in Lemma 4.1 and Step 1 | stated in `hyp:L` |
| `c^-, c^+ >= 0` real, `mu_i >= 0` | domination by `D(z)`, conjugation symmetry | `Q` a generator, `mu` a law |
| `F` irreducible | not used | — |

Nothing beyond the hypotheses of `hyp:L` is needed. In particular no reversibility and no
condition on `i`.

## 7. Numerical check

Script `09_hypL_check.py`, output `09_hypL_check_output.txt`, run with `py -I` from this folder.
Two faces with four states, `F = {0, 1, 2, 3}`, `i = 3`, `G = {0, 1, 2}`, so `|G| = 3` and `m = 2`:

- the non-reversible 4-cycle `q_{j, j+1} = 2`, `q_{j+1, j} = 1` (indices mod 4), uniform start,
  `beta = (0.5, 0.3, 0.2)`; on `G` this is the path `0 - 1 - 2`, `c^- = (1, 0, 2)`, `c^+ = (2, 0, 1)`;
- the complete graph on four states with the off-diagonal rates
  `(0, 1, 2, 0.5; 1.5, 0, 1, 2; 0.5, 2, 0, 1; 2, 0.5, 1.5, 0)`, start `(0.1, 0.2, 0.3, 0.4)`,
  `beta = (0.4, 0.35, 0.25)`.

Both are non-reversible (the Kolmogorov cycle criterion fails by a factor `16` and `12`).

What is computed.

1. The exact `f^(z)_G(S beta) = e^{-<d(z), S beta>} H_z(S beta)` by a dynamic program over the word
   length (`log_H_words`): the state at length `L` is the array over `(m_1, m_2)` and the last
   letter of the weighted sum of words with counts `(m_1, m_2, L - m_1 - m_2)`, with the factors
   `s_j^{m_j - 1}/(m_j - 1)!` folded into the recursion and the layers rescaled. This is the word
   sum of Lemma `lem:layer-exact` and does not use the torus. It is checked against a direct
   enumeration of `W(m)` at `S = 2.5` (check (d)).
2. The prediction `S^{-1} C_G(beta, z) e^{-S J_G(beta, z)}` from the complex tilt: Newton's method
   on the critical equations of `psi -> Psi_beta(e^psi) - z P_beta(e^psi)` in complex `psi`,
   continued from the real tilt at `z = 0`; then `J_G = <d(z) - theta, beta>` and `C_G` by Definition
   `def:tilt` with `A(z)`, `mu^(z)`, `e^(z)` and the principal root of `det Sigma_beta(z)`.
3. Check (a): the torus critical point `zeta'` of `Phi_z` by Newton's method equals `theta'(beta, z)`
   from the complex tilt, `g_z(theta') = theta_1`, `det J beta_1^2 = prod theta_j^2 det Sigma`, and
   the torus amplitude `(2 pi)^{-1} det J^{-1/2} b_z prod zeta_j` equals the algebraic `C_G`. This is
   Lemma 4.1(e) continued to complex `z`.
4. Check (b): the 2-torus integral of Lemma 3.1 at the radii `|zeta'|` rotated by `arg zeta'`
   (trapezoidal rule with `512^2` points, exponentially accurate for an analytic periodic
   integrand) against the word sum.
5. Check (c): the least eigenvalue of `Re J(beta, z)` on circles `|z| = 0.05` to `0.8`.
6. The main table: `eps = f^(z)_G(S beta) / prediction - 1` and `S |eps|` for `S = 10, 20, 40, 80,
   160` and `z` in `{0, 0.1, -0.1, 0.1 i, -0.1 i, 0.1 e^{3 pi i/4}, 0.2 i, 0.2 e^{pi i/3}}`.

A second script, `09_hypL_phase_check.py` with output `09_hypL_phase_output.txt`, checks Lemma
4.1(d) by central differences in `phi`: at the complex critical point, `|grad_phi Psi(0)|` is at
most `2e-8` and `-grad^2_phi Psi(0)` agrees with `Z_c grad^2 Phi_z Z_c` to a relative `7e-8` (the
truncation level of the step `1e-4`), at four complex `z` for each chain.

Results (`09_hypL_check_output.txt`, total run time about 7 minutes).

Check (d). The dynamic program agrees with the direct enumeration to `1e-15` (cycle) and `3e-11`
(K4, where words of length above 32 still contribute at this level).

Check (a). At all nine `z`, `|zeta' - theta'(beta, z)|`, `|g_z(theta') - theta_1|`,
`|C_torus/C_alg - 1|` and `|det J beta_1^2/(prod theta_j^2 det Sigma) - 1|` are below `3e-15`. So
the complex tilt is the torus critical point, and the two formulas for `C_G(beta, z)` agree, for
complex `z` as Lemma 4.1 and Theorem 5.1 assert.

Check (b). Where the word sum is accurate (cancellation exponent `kappa` below about 20), it
agrees with the 2-torus integral through the complex critical point to between `1e-17` and `1e-13`.
This is Lemma 3.1 at complex weights and complex radii. For larger `kappa` the discrepancy is
`1e-16 e^kappa` as predicted (`kappa = 28.6` gives `5e-6`, `kappa = 38.8` gives total loss), and
those cells are marked `*` in the table, where the torus identity supplies the exact value.

Check (c), the real part of the Hessian. `lambda_min(J(beta, 0))` is `0.583` (cycle) and `1.086`
(K4). Along rays `z = rho e^{i ang}`, `Re J(beta, z)` stays positive definite up to `rho = 1` in
all 16 directions tested except: for the cycle, the continuation of the critical point folds on
the negative real axis at `rho = 0.070` (the Hessian becomes singular, `det J` goes from `2.02` at
`z = 0` through `0.70` at `z = -0.065` to `0`), and `Re J` loses positivity at `rho = 0.885` in the
directions `3 pi/4` and `5 pi/4`; for K4, `Re J` loses positivity at `rho = 0.350` on the negative
real axis and nowhere else below `rho = 1`. On the negative real axis `-z P_beta` is convex, so the
critical point of `Psi_beta - z P_beta` is a saddle there, and it can run away; that is the fold.
So the disc of Theorem 5.1 for the cycle at this `beta` has radius below `0.070`. This is
consistent with the theorem, whose `z_0` depends on the chain and on `Kc`, and it shows that the
region of validity is not a disc: the expansion holds at `|z| = 0.2` in other directions.

The main table. `S |eps|` for `S = 5, 10, 20, 40, 80, 160`, word sum where unmarked and torus
identity in the cells marked `*`.

4-cycle, `beta = (0.5, 0.3, 0.2)`:

| `z` | 5 | 10 | 20 | 40 | 80 | 160 |
|---|---|---|---|---|---|---|
| `0` | 0.3641 | 0.3536 | 0.3499 | 0.3483 | 0.3475 | 0.3471 |
| `0.1` | 0.2793 | 0.2751 | 0.2734 | 0.2727 | 0.2723 | 0.2721 |
| `-0.05` | 0.5110 | 0.5120 | 0.5238 | 0.5352 | 0.5433 | 0.5483* |
| `0.1 i` | 0.3303 | 0.3245 | 0.3220 | 0.3209 | 0.3203 | 0.3200* |
| `-0.1 i` | 0.3303 | 0.3245 | 0.3220 | 0.3209 | 0.3203 | 0.3200* |
| `0.1 e^{3 pi i/4}` | 0.4687 | 0.4538 | 0.4458 | 0.4425 | 0.4410* | 0.4402* |
| `0.05 e^{3 pi i/4}` | 0.4012 | 0.3868 | 0.3823 | 0.3805 | 0.3797 | 0.3792* |
| `0.2 i` | 0.2691 | 0.2678 | 0.2668 | 0.2664 | 0.2661 | 0.2660* |
| `0.2 e^{pi i/3}` | 0.2476 | 0.2456 | 0.2446 | 0.2442 | 0.2440 | 0.2439 |

K4, `beta = (0.4, 0.35, 0.25)`:

| `z` | 5 | 10 | 20 | 40 | 80 | 160 |
|---|---|---|---|---|---|---|
| `0` | 0.1818 | 0.1807 | 0.1802 | 0.1799 | 0.1798 | 0.1797 |
| `0.1` | 0.1612 | 0.1603 | 0.1599 | 0.1597 | 0.1596 | 0.1595 |
| `-0.1` | 0.2125 | 0.2110 | 0.2103 | 0.2100 | 0.2099 | 0.2098 |
| `0.1 i` | 0.1789 | 0.1778 | 0.1773 | 0.1771 | 0.1770 | 0.1769 |
| `-0.1 i` | 0.1789 | 0.1778 | 0.1773 | 0.1771 | 0.1770 | 0.1769 |
| `0.1 e^{3 pi i/4}` | 0.1992 | 0.1978 | 0.1972 | 0.1969 | 0.1968 | 0.1967 |
| `0.05 e^{3 pi i/4}` | 0.1906 | 0.1893 | 0.1888 | 0.1885 | 0.1884 | 0.1883 |
| `0.2 i` | 0.1719 | 0.1709 | 0.1704 | 0.1702 | 0.1701 | 0.1700 |
| `0.2 e^{pi i/3}` | 0.1568 | 0.1560 | 0.1556 | 0.1554 | 0.1553 | 0.1553 |

Reading. In every row `S |eps|` tends to a constant, and the ratio of consecutive entries is
within `0.3` percent of `1` from `S = 40` on (within `2.3` percent for the cycle at `z = -0.05`,
which sits near the fold at `-0.070`, where the next-order constant is large; its ratios decrease
toward `1`). So the error is `C/S` and not smaller: the `O(1/S)` of Hypothesis L is attained, with
`C` between `0.16` and `0.55` here. For the K4 chain no cell needed the torus value. The complex
parts of `eps` have the conjugation symmetry `eps(zbar) = conj eps(z)` exactly, as Lemma 4.1(c)
predicts. At real `z` the error is real and negative in all cases tested.

Two lessons from a first run, kept here because they affect any reimplementation. Newton's
method for the complex tilt started at the real tilt of `z = 0` jumped to a different critical
point for the cycle at `z = -0.1`, past the fold; the script now continues the solution along
the segment `[0, z]` in 25 steps. And the word sum with complex weights cancels by the factor
`e^kappa`, with `kappa` growing linearly in `S` (`kappa/S` is `0.18` for the cycle at `z = 0.1 i`
and `0.03` for K4), so double precision cannot evaluate it beyond `S` of about `100` for the cycle
at `|z| = 0.1`. The torus through the complex critical point has no such cancellation, which is
the numerical face of the proof. The three warnings `Lcap reached` in the stderr file come from
check (d) at `S = 2.5`, where the stopping rule asks for 40 quiet layers inside the cap `80`;
the truncation error there is below `1e-30`. The `RuntimeWarning`s come from the fold scan past
the fold, where the continuation is allowed to fail and returns `NaN`.

No statement of Sections 2 to 6 is deduced from these numbers.

## 8. What this means for the paper

Nothing in the paper was edited. If the proof above is adopted:

- Hypothesis `hyp:L` becomes a lemma (Lemma 2.2, Lemma 3.1, Lemma 4.1, Theorem 5.1 of this note,
  which fit the style of Appendices `app:torus` and `app:laplace`; Lemma 2.2 is Remark
  `rem:laplace-uniform` with two hypotheses weakened, and Lemma 3.1 is Lemma `lem:torus` with a
  dominating system).
- Theorem `thm:layer` becomes unconditional for every irreducible `F` with `k >= 2` whose facet
  `G` satisfies (H); the sentences "If `k >= 4`, assume that Hypothesis L holds" in the statement,
  the paragraph after the theorem, the last sentence before Lemma `lem:L-two`, the corresponding
  sentence of the section opening, and the open-problems paragraph change accordingly. Lemma
  `lem:L-two` can stay as the closed form for `|G| = 2`.
- The abstract's "which we prove for faces with at most three states" can be dropped for part (a)
  and the reversible part (c); the restriction to reversible `Q` or `x <= C T^{1/3}` for the
  relative Bessel form is unchanged, since it comes from the cubic term and not from `hyp:L`.

Status: proved.
