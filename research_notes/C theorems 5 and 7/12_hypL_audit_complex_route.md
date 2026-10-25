# Audit of the complex-phase proof of Hypothesis L (note 09)

Date October 24, 2026. Base commit `0ffc041`. Files audited: `09_hypL_complex_laplace.md`,
`09_hypL_check.py`, `09_hypL_phase_check.py` and their outputs. Paper files read from
`git show 0ffc041:kagey-problems/problem131/paperC/{sec_boundary,app_torus,app_laplace,sec_secondorder}.tex`,
since `paperC2` no longer holds `sec_boundary.tex`. Written files: this note,
`12_hypL_audit_check.py` and `12_hypL_audit_check_output.txt`. The status lines of note 09 were
ignored. Every step marked passed below was redone by hand. Note 10 was read only after the audit
was finished, for the comparison at the end.

## The claim, normalized

Fix a generator `Q` and a start law `mu` on `F = G u {i}`. Assume (H) for `G`: `G` is irreducible
and `mu(G) > 0`. Assume `g = |G| = k - 1 >= 2` and that `F` is irreducible. Fix a compact set
`K` in the open simplex on `G`. Put `m = g - 1`, `A(z) = A_G + z offdiag(c^- c^+T)`,
`d(z) = q_G - z c^- o c^+`, `mu^(z) = mu_G + z mu_i c^+`, `e^(z) = 1 + z c^-`, and let

    f^(z)_G(s) = e^{-<d(z), s>} sum_{m in Z_{>=1}^G} W_z(m) prod_j s_j^{m_j-1}/(m_j-1)!

be the word series of `lem:layer-exact`.

**Claim (hyp:L).** There are `z_0 > 0`, `C < inf` and functions `J_G(beta, z)`, `C_G(beta, z)` on
`K x {|z| < 2 z_0}` with these properties. They are holomorphic in `z`, jointly continuous, and
real for real `z`. For real `0 <= z < 2 z_0` they equal the rate `<d(z) - theta(beta, z), beta>`
of `Q_G(z)` and the constant
`(mu^(z) . r_beta(z))(l_beta(z) . e^(z)) / ((2 pi)^{m/2} sqrt(det Sigma_beta(z)))`. Also
`C_G(beta, 0) = C_G(beta) > 0`. Finally, for all `beta` in `K`, real `S >= 1` and complex
`|z| <= z_0`,

    f^(z)_G(S beta) = S^{-m/2} C_G(beta, z) e^{-S J_G(beta, z)} (1 + eps),   |eps| <= C/S.

`z_0` and `C` may depend on `Q`, `mu`, `i` and `K`, and on nothing else.

## Verdict

**Proved as written.** Hypothesis L follows from Lemmas 2.1, 2.2, 3.1 and 4.1 and Theorem 5.1 of
note 09, under the stated hypotheses. I found no gap that carries weight. There are three small
defects. None changes the claim.

- (D1) Fact (F6) cites `prop:layer-constants`(ii) for the continuity of the real tilt in `z`.
  That proposition assumes `F` irreducible, which conflicts with the remark that `F` is not
  needed. Lemma 4.1(e) does not need the citation. A direct argument is given under
  obligation 3.
- (D2) Section 7 says that the disc of Theorem 5.1 for the cycle "has radius below 0.070". The
  hypothesis asks for holomorphy on `|z| < 2 z_0`, so the fold forces `z_0 <= 0.035` for any `K`
  that contains `beta = (0.5, 0.3, 0.2)`. This is a wording slip. The theorem only asserts that
  some `z_0` exists.
- (D3) Two output slips with no effect on the mathematics. The script prints "Kolmogorov
  defect = 0.0000" for the 4-cycle, because it tests only 3-cycles and the 4-cycle has none. The
  note's "fails by a factor 16" refers to the 4-cycle loop and is correct. The script comment
  puts the fold at `-0.066`, the note at `-0.070`.

## Obligation matrix

| # | Obligation | Mark |
|---|---|---|
| 1 | Lemma 2.2 (Laplace lemma, complex `Psi(0)`, complex `J` with `Re J >= sigma I`) | passed |
| 2 | Lemma 3.1 (torus identity, complex weights, general end vector, range of radii) | passed |
| 3 | Lemma 4.1 (critical point, uniform contraction, holomorphy, Hessian, sign of `Re J`) | passed (D1 is a citation defect with a direct repair) |
| 4 | Theorem 5.1: no contour shift is needed | passed |
| 5 | Uniformity: constants from `K` and `z_0` only, `z_0` from `K` only | passed (for a fixed chain) |
| 6 | Irreducibility of `F` not needed | passed (after D1) |
| 7 | The constant equals `C_G(beta, z)`, by hand for 2 states | passed |
| 8 | Numerics: exact quantity, rerun with `py -I`, new facet with 4 states, the fold | passed (D2, D3 cosmetic) |

## Decisive evidence

### 1. Lemma 2.2

*One dimension, by hand.* Let `Psi(phi) = Psi_0 - J phi^2/2 + Psi_3 phi^3/6 + R_4(phi)` on
`[-pi, pi]`, with `J = a + i b`, `a >= sigma > 0`, `|R_4| <= B phi^4/24`, and a gap `eta` for
`|phi| >= epsilon`. Put `phi = x/sqrt T`. The integrand near `0` is
`e^{T Psi_0} T^{-1/2} e^{-J x^2/2} (1 + T^{-1/2}(Psi_3 x^3/6 + a_1 x/a_0) + O(T^{-1}(1+|x|)^6 e^{sigma x^2/4}))`.
The modulus of the weight is `e^{-a x^2/2} <= e^{-sigma x^2/2}`, and the remainder in brackets
gains at most `e^{sigma x^2/4}`, so its integral is `O(1/T)`. The odd terms vanish because the
weight `e^{-J x^2/2}` is even and absolutely integrable. The Gaussian integral is
`int e^{-J x^2/2} dx = sqrt(2 pi) J^{-1/2}`. Both sides are holomorphic on `Re J > 0` and agree
for `J > 0`. Since `|arg J| < pi/2`, `J^{-1/2}` is the principal root, with argument in
`(-pi/4, pi/4)`. The tail outside the cube is `O(e^{-sigma epsilon^2 T/4})`, and the far region
is `O(e^{-eta T})`, times `|e^{T Psi_0}|`. Relative to the main term this costs the factor
`|J|^{1/2} <= B^{1/2}`. So `I = e^{T Psi_0} sqrt(2 pi/(T J)) (a_0 + O(1/T))`, with a constant
that depends on `sigma`, `B`, `B_a`, `epsilon`, `eta` only. This agrees with Lemma 2.2 for
`m = 1`.

*General case, step by step against `app_laplace.tex`.* The paper uses the reality of
`Psi(alpha, 0)` and of `J` in exactly three places.

- Localization. It needs only `Re Psi - Re Psi_0 <= -eta` and `|e^{T Psi_0}| = e^{T Re Psi_0}`.
  Hypothesis (iii) of Lemma 2.2 gives this.
- Cubic remainder. `|R| <= (m^3/6) B_Psi ||phi||^3 <= (sigma/4)|phi|^2` uses only bounds on the
  third derivatives and `m^3 B_Psi epsilon <= (3/2) sigma`. This holds for complex `R` (Taylor
  with integral remainder). So `|w(x)| <= sigma |x|^2/4`.
- Integration. It needs `|e^{-x^T J x/2}| = e^{-x^T (Re J) x/2} <= e^{-sigma |x|^2/2}` for real
  `x`. This is true because `x^T (Im J) x` is real. The product with `e^{|w|}` is then at most
  `e^{-sigma |x|^2/4}`. The tail and remainder bounds follow as in the paper.

The odd polynomial still integrates to zero. The Gaussian integral is Lemma 2.1. Its proof is
correct. `det J != 0` on `S_m^+`, since `Re(x^* J x) = x^*(Re J) x > 0` for complex `x != 0`.
The continuous root exists because `S_m^+` is convex. The identity theorem applies, since the
real positive definite matrices form an open subset of the real points of the domain. The final
division uses `|det J| <= (m B_Psi)^m` (Hadamard, complex form). Note that for `m >= 2` the
continuous branch need not be the principal root of `det J`. The proof never assumes that it
is, and near `z = 0` the two coincide. **Passed.**

### 2. Lemma 3.1

Step 1. `varrho(D'(z) - diag s') < 0` gives `varrho(diag(s')^{-1} D'(z)) < 1`. The entries of
`Z'^{-1} A'(z)` are bounded in modulus by those of `diag(s')^{-1} D'(z)` when `|z_j| >= s_j`.
Then the Neumann series converges absolutely, and termwise domination gives `|g_z| <= g_D(s')`
and `|b_z| <= b_D(s')`. The entrywise bounds `|A(z)| <= D(z)`, `|mu^(z)| <= mu_D` and
`|e^(z)| <= e_D` hold because `c^-, c^+, mu_i >= 0`.

Step 2. Choose `s_1 > g_D(s')`. Then `varrho(S^{-1} D(z)) < 1`, by the paper's vector
`v = (1, X_D(s')(b_{1,D} + eps 1))`.

Step 3. On the full torus `|z_j| = s_j`, the word expansion of `mu^(z)T (Z - A(z))^{-1} e^(z)`
is dominated by `mu_D^T (S - D)^{-1} e_D < inf`, uniformly. So termwise integration is
justified. `A(z)` has zero diagonal, so the words have no equal neighbours. Cauchy's formula
returns `sum_m W_z(m) prod t_j^{m_j-1}/(m_j-1)!`, which is exactly the series of
`lem:layer-exact`.

Step 4. I redid the block inversion:
`mu^T M^{-1} e = (mu_1 + mu'^T X b_1)(e_1 + a_1^T X e')/(z_1 - g) + mu'^T X e'`. It is correct
with the general end vector. Since `|g_z| < s_1`, the residue gives `e^{t_1 g_z} b_z`.

So the representation is an identity for every `s'` with `varrho(D'(z) - diag s') < 0`. This
holds with no periodicity argument and no shift. Lemma 4.1(a) gives this condition for every
real `s'` with `||s' - theta'(beta)|| <= 3 r_0` and `|z| <= z_1`. Theorem 5.1 Step 1 gives
`||rho' - theta'|| <= B |z| <= r_0`. So the radii `rho_j = |zeta_j|` are inside the range.
**Passed.**

### 3. Lemma 4.1

(a), (b): continuity of the Perron root in `(|z|, s')` and Cauchy estimates on polydiscs that
stay inside `|z_j| > theta_j - 3 r_0`. Correct.

(c): `T(z') = z' - H(beta)^{-1} F(beta, z, z')` has Lipschitz constant `B_1 B_2(|z| + r)` and
moves the centre by at most `B_1 B_3 |z|`. With `B_1 B_2 (z_2 + r) <= 1/2` and
`B_1 B_3 z_2 <= r/2`, `T` is a 1/2-contraction of the closed ball into itself. The constants
`B_1, B_2, B_3` are uniform on `K` by compactness. The iterates are holomorphic in `z` and
converge uniformly, so the limit is holomorphic. The coefficients are real, so
`F(beta, zbar, conj z') = conj F(beta, z, z')`. The ball is centred at a real point, so
uniqueness gives the conjugation symmetry. Correct.

(d): with `w_j = zeta_j e^{i phi_j}`,
`d^2 Psi/d phi_j d phi_k = -w_j w_k Phi_{jk} - delta_{jk} w_j Phi_j`. The last term vanishes at
the critical point, so `-grad^2_phi Psi(0) = Z_c grad^2 Phi_z Z_c`. Correct. The phase check
confirms it by finite differences: the rerun output is identical to the stored one, with
relative agreement `1e-8` to `7e-8`.

(e), with D1: the note cites `prop:layer-constants`(ii), which assumes `F` irreducible, for the
continuity of `theta(beta, z)`. A direct argument avoids it. For real `z` in `[0, z_1)`,
`zeta'` is real by (c) and positive, since `r_0 < theta_j/4`. Also `A(z) = D(z) >= 0`, so
`varrho(A'(z) - diag zeta') < 0`. Then `(1, X_z(zeta') b_1(z)) > 0` lies in the kernel of
`A(z) - diag(g_z(zeta'), zeta')`. So `theta := (g_z(zeta'), zeta')` has Perron root `0`.
Differentiating `lambda(g_z(z'), z') = 0` gives `d_j g_z = -pi_j/pi_1`, with `pi = l o r`
(Lemma `lem:perron` after the similarity by `diag r`). The critical equation
`beta_1 d_j g_z + beta_j = 0` then forces `pi = beta`. So `l = beta/r` satisfies the stationarity
`l^T(A(z) - diag theta) = 0`, and `r` is the minimizer of the convex dual. Hence `zeta'` is the
tilt of `Q_G(z)`. This uses neither continuity in `z` nor `F`.

Sign of `Re J` on the rotated torus. Lemma 2.2 uses the Hessian only at `phi = 0`. Away from `0`
it needs the gap (iii), and near `0` the cubic bound with `epsilon` fixed from `B_Psi` and
`sigma`. Theorem 5.1 Step 1 (delta) gets the gap from `(F3)` at `z = 0` and uniform continuity
of `Re[Psi(beta, z, phi) - Psi(beta, z, 0)]` on the compact set `P_1 x T^m`. The order of the
choices is consistent: `B_Psi` is fixed on `P_1` before `z_0`, then `epsilon`, then `eta`, then
`z_0`. So no sign condition on `Re J` away from the critical point is needed, and none is
missing. **Passed.**

### 4. No contour shift

Lemma 3.1 at the radii `rho'` gives `H_z(S beta)` exactly as a torus integral. The translation
`phi' = phi + Arg zeta'` is a measure-preserving map of `T^m`. It turns `rho_j e^{i phi'_j}`
into `zeta_j e^{i phi_j}`, and turns the integrand into `e^{S Psi(beta, z, phi)} chi(beta, z, phi)`
pointwise. So the identity is exact. No term is dropped by periodicity, and no deformation
between radii is used. The prefactor `(2 pi)^{-m} (2 pi/S)^{m/2} = S^{-m/2} (2 pi)^{-m/2}` gives
the stated power of `S` and the stated `C_G`. **Passed.**

### 5. Uniformity

Every constant comes from compact sets: `K x {|z| <= z_1/2} x T^m`, or the closed balls of
Lemma 4.1 over `K`. `r_0, z_1, c_0, B, B_1, B_2, B_3, sigma_0, B_Psi, B_a, epsilon, eta, c_chi`
depend only on `K` and the chain. `z_0` is chosen after them. `C` comes from Lemma 2.2 and
`c_chi`. `S >= 1` is covered, since Lemma 2.2 holds for all `T >= 1`. **Passed.**

### 6. Irreducibility of `F`

Domination uses `c^-, c^+ >= 0`, and irreducibility of `D(z)` comes from `A_G`. Positivity of
the amplitude uses `mu(G) > 0`. With the repair of D1, `F` is used nowhere. If `c^-` or `c^+`
vanishes, the argument still runs. The claim is then trivial in part, but true. **Passed.**

### 7. The constant

*Two states, by hand.* Let `G = {1, 2}` and `tau = a_12 a_21`. Then `X = 1/z_2`,
`g = tau/z_2`, `b = (p_1 + p_2 a_21/z_2)(e_1 + a_12 e_2/z_2)`, and
`Phi = beta_1 tau/z_2 + beta_2 z_2`. The critical point is `zeta = sqrt(beta_1 tau/beta_2)`,
with `Phi(zeta) = 2 sqrt(beta_1 beta_2 tau)`. This gives
`J_G = <d, beta> - 2 sqrt(beta_1 beta_2 tau)`, as in `lem:L-two`. The Hessian is
`J = zeta^2 Phi'' = 2 beta_1 tau/zeta = 2 sqrt(beta_1 beta_2 tau)`. Next,
`b zeta = p_1 e_1 zeta + p_2 e_2 tau/zeta + p_1 a_12 e_2 + p_2 a_21 e_1 = U + V`, with
`zeta = sqrt(tau beta_1/beta_2)` and `tau/zeta = sqrt(tau beta_2/beta_1)`. So
`(2 pi)^{-1/2} J^{-1/2} b zeta = (U + V)/(sqrt(4 pi)(tau beta_1 beta_2)^{1/4})`. This is the
constant of `lem:L-two`, with the same principal branch for `z` near `0`.

*General `g`, real `z`.* `det J = prod theta_j^2 det Sigma/beta_1^2` and
`b_z(theta') = (mu^(z) . r)(l . e^(z))/beta_1`. Both follow from the computation in the proof of
`thm:local`, applied to `A(z) >= 0`. Together they give the constant of
`sec:layer-setting`. Numerically, my script finds that the torus constant and the constant of
Definition `def:tilt` agree to 12 digits at `z = 0, 0.05, 0.1`, for both new chains. They
also agree with the closed form of `lem:L-two` to `5e-16` at complex `z`. **Passed.**

### 8. Numerics

*What the script computes.* `log_H_words` in `09_hypL_check.py` is a dynamic program over the
word length. It uses the weights `A(z)` (zero diagonal), `mu^(z)` and `e^(z)`. It folds in the
factors `s_j^{m_j-1}/(m_j-1)!` (the multiplier is `s/(k-1)` when a count goes from `k-1` to
`k`) and keeps only `m >= 1`. Then it multiplies by `e^{-<d(z), s>}`. This is the exact quantity
of `hyp:L`, not a surrogate. The prediction uses `S^{-1}`, which is `S^{-m/2}` for `m = 2`.

*Rerun.* `py -I 09_hypL_check.py` and `py -I 09_hypL_phase_check.py` reproduce the stored
outputs line for line. Only the timing column differs.

*Independent check* (`12_hypL_audit_check.py`). The script imports nothing from 09 or 10. Its
word dynamic program works for any number of letters. I checked it against brute-force
enumeration for `g = 2, 3, 4`: the agreement is `2e-16`, `2e-15` and `2e-11`, and the last
figure falls as the enumeration length grows. The prediction comes from my own Newton
continuation of the torus critical point. I ran two new chains.

- A facet with four states (`|G| = 4`, `m = 3`, face with five states). The rates are
  non-reversible, `c^- = (0.8, 0, 1.2, 0.3)`, `c^+ = (0.5, 1, 0, 0.9)`, `mu_i = 0.25`, and
  `beta = (0.3, 0.25, 0.2, 0.25)`. Values of `S |eps|` for `S = 4, 8, 16, 32`:
  - at `z = 0`: 0.4328, 0.4359, 0.4374, 0.4382;
  - at `z = 0.08 i`: 0.4331, 0.4361, 0.4376, 0.4384;
  - at `z = 0.1 e^{2 pi i/3}`: 0.4394, 0.4429, 0.4445, 0.4454;
  - at `z = -0.08`: 0.4423, 0.4462, 0.4481, 0.4491.

  The consecutive ratios fall as `1.007, 1.0035, 1.0018` toward `1`, so the error is `C/S` with
  the power `S^{-3/2}`. The cancellation exponent stays below `1.4`, so every cell is accurate.
- A new face with four states (`|G| = 3`), with `mu_i = 0.4` and zeros in `c^-` and `c^+`.
  `S |eps|` is about `0.21` at six values of `z` with `|z| <= 0.12`. The ratios are
  `0.995, 0.998, 0.999, 0.9995` for `S` from 5 to 80.

On both chains `Re J` stays positive definite on the segments used. Its least eigenvalue is
`>= 0.50` for `|z| <= 0.2`, and no fold occurs there.

*The fold.* For the cycle in note 09, check (c) shows `det J -> 0` along the negative real axis
near `z = -0.070`, which is consistent with a branch point of `zeta'`. `J_G` is then not
holomorphic on any disc of radius above `0.070` about `0`. The hypothesis asks for holomorphy on
`|z| < 2 z_0`, so `z_0 <= 0.035` for that `beta` (D2). The theorem only claims that some
`z_0 > 0` exists, so there is no inconsistency. The cycle's main table uses `z = 0.1 i` and
`0.2 i`, which are outside such a disc. Those rows test the representation and the expansion
beyond the theorem's disc. They do not test the theorem itself. **Passed.**

## Remaining gap

None that carries weight. D1 should be fixed in any write-up by the direct argument under
obligation 3. D2 and D3 are wording and output slips.

## Strongest safe statement

Let `G` satisfy (H) with `|G| >= 2`. Let `c^-, c^+ >= 0` and `mu_i >= 0` be arbitrary, with no
condition on `F`. Let `K` be a compact set in the open simplex on `G`. Then there are
`z_0 > 0` and `C`, depending only on `Q`, `mu`, `i` and `K`, such that Hypothesis L holds with
`J_G(beta, z) = <d(z), beta> - Phi_z(zeta'(beta, z))` and
`C_G(beta, z) = (2 pi)^{-m/2} det J(beta, z)^{-1/2} b_z(zeta') prod_j zeta_j`. The branch is the
continuous one on `Re J > 0`, and the functions are holomorphic on `|z| < 2 z_0`. `z_0` is not
explicit. It is at most half the distance from `0` to the nearest singularity of the continued
critical point (for example, `z_0 <= 0.035` for the 4-cycle at `beta = (0.5, 0.3, 0.2)`).
Theorem `thm:layer` becomes unconditional for all `k >= 2`, given its other hypotheses.

## Comparison with the spectral route (note 10, read after the verdict)

Note 10 states `C_G = (2 pi)^{-m/2} det H_Phi^{-1/2} (mu^(z) . r)(l . e^(z)) det Theta/<theta, beta>`,
with Lemma H: `det H_Phi = det Theta^2 det Sigma/<theta, beta>^2` for real `z`. This reduces to
`(mu^(z) . r)(l . e^(z))/((2 pi)^{m/2} sqrt(det Sigma_beta(z)))`, the same real constant that
note 09 reaches through `det J = prod_{j>=2} theta_j^2 det Sigma/beta_1^2`. Both constants are
holomorphic on a disc about `0` and agree on `[0, 2 z_0)`, so they agree on the common disc.
Both rates equal `<d(z) - theta(beta, z), beta>`. The asymptotic also fixes the pair uniquely: if
`S^{-m/2} C e^{-S J}` and `S^{-m/2} C' e^{-S J'}` both match `f` up to `1 + O(1/S)` for all real
`S >= 1`, then `J = J'` and `C = C'`. Neither route makes `z_0` explicit. The two routes differ
only in how the Hessian is normalized (torus variables against spectral variables), and the
determinant identities absorb the difference.
