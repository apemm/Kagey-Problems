# Audit of route T5-B: class-uniform finite-horizon recovery (Theorem 5b)

Date: October 24, 2026. Base checkpoint `6add913`. Read-only audit; no manuscript or note was
edited.

Audited: `research_notes/C theorems 5 and 7/02_T5_class_uniform.md` (all of it), against the
target contract `00_targets.md` (Target 1) and the printed proofs it uses:
`paperC/sec_model.tex` (run expansion, (2.2) `eq:vertexmax`, Lemma 2.3 `lem:continuum`),
`paperC/sec_firstorder.tex` (Proposition 3.2 `prop:rate`, the set `V_F`, Lemma 3.3 `lem:upper`),
`paperC/sec_secondorder.tex` (Definition 4.1, Proposition 4.2, Theorem 4.4 `thm:local`, Lemma 4.5
`lem:discrete`, Theorem 4.6 `thm:facemax`, Theorem 4.7 `thm:crossing`, with proofs),
`paperC/app_torus.tex` (Lemma A.1, proof of Proposition 4.2(a), Lemma A.2 `lem:torus`, proofs of
Lemma 3.3, Theorem 4.4 and Lemma 4.5), `paperC/app_laplace.tex` (Lemma B.1 `lem:laplace`), and
`research_notes/Occupation novelty and compact advances/11_C_ready_to_draft_outline.md` Sections 1,
2, 3 and 5 (design C-I1, stability C-I3, the counterexample over all starts).

Scripts: `pair_entry_uniform.py` and its output `pair_entry_output.txt`, kept in a local scratch
folder `audit_t5` outside the repository (copy them next to this file if they are to be kept).

## 0. Verdict in one paragraph

The note's argument is sound. Parts (a), (b) and (c) of Theorem U6 are proved as written, up to
three small slips that change no statement (Section 5, items 3 to 5). Part (d) is **conditional on a
named input**, the stability bound C-I3 of the outline, which is a research-note result and is not
proved in the paper sources or in the note. The finite-`N` suppression lemma (Lemma U5) also cites
the suppression lemma of C-I1 from the outline. I re-derived its two score gaps (3/4 and 1/2) by hand
(Section 3.7), so that input is now checked, but the paper has to print it. The remark after Theorem
U6, which lets `mu_*` decrease with `N` as long as `log(1/mu_{*,N}) = o(log N)`, is **not proved**
by the note's compactness argument, because the constants of Lemmas U2 and U3 are bounded through
`mu_*`. It is true, by a linearity-in-`mu` argument I give in Section 5 item 2, but the note should
either add that argument or drop the remark. I found no gap in the uniformity mechanism itself. Every
constant is either a continuous function on a compact set or comes from a finite cover that can be
taken jointly in the parameter. I recomputed the expansion of `t_{ij,N}`, including the sign, the
`1/2` and `c_ij`, and it agrees with the note.

## 1. Claim (i): the field factors out exactly

**Fact 1.** For `supp n = F` and `alpha = n/N`, `Pr_mu(n) e^{Tv.n/N} = P_N(n) e^{T v.alpha}`.
Define `f^v_T(alpha) = T^{k-1} e^{-T<q - v, alpha>} H(T alpha)`. `H` (sec_model, before Lemma 2.3) is
built from `W(m)`, which involves only `mu` and the off-diagonal rates, so
`f^v_T = e^{T v.alpha} f_T`. The ratio `Pr_mu(n) e^{Tv.n/N} / (N^{-(k-1)} f^v_T(n/N))` is therefore
literally the ratio `P_N(n)/(N^{-(k-1)} f_T(n/N))` of Lemma 4.5. Correct, with the same constants
and the same range `1 <= T <= N^{1/2}`.

**Fact 2.** Definition 4.1: `r_alpha` maximizes `u -> <q - A_F u/u, alpha>` (here `A_F` is the
off-diagonal part, as in the paper, not the `-Q_F` of the target notation). Replacing `q` by `q - v`
adds the constant `-<v, alpha>`, so `r_alpha`, `theta(alpha)`, `l_alpha`, `Z_alpha`, `Gamma_alpha`,
`Sigma_alpha` and `C_F(alpha)` do not change, and `I_F` becomes `I_F - v.alpha`. Since
`f^v_T = e^{T v.alpha} f_T` exactly, the local law for `f^v_T` follows from Theorem 4.4 by
multiplication, with the same `O(1/T)` constant. No re-proof is needed. Correct.

**The minimizer.** `I_F - v.alpha` is the rate of Proposition 3.2 for the Metzler matrix
`Q_F + diag v`. I checked that the proof of Proposition 3.2(a), (b) and (d) uses only that the
off-diagonal pattern is strongly connected. The lower bound writes `Q_{F'} = B - cI`, the value at
`alpha*` uses only the eigenvector equation, and (d) uses Perron monotonicity for irreducible Metzler
matrices. It never uses `q_i = sum_j q_ij`. Part (c) does use conservativity, but it is not needed.
So `alpha*_F(v) = l circ r` for `Q_F + diag v`, `lambda_F(v) = -varrho(Q_F + diag v)`, and the
minimizer is unique on the closed face, boundary included. Correct.

Claim (i) holds.

## 2. Claim (ii): the uniformity mechanism, step by step

### 2.1 Compactness of the class (Lemma U0)

`q_i = S_ii <= ||S||_2 <= R`, `q_ij q_ji = S_ij^2 >= b^2` and `q_ij <= R` give
`b^2/R <= q_ij <= R` on edges. The pattern is preserved under limits, reversibility (Kolmogorov) is
closed, and `pi` and hence `S` depend continuously on `Q`. So the class is compact. The start set
`{min mu >= mu_*}` and the field box are compact. Correct.

### 2.2 The Laplace lemma with a parameter (Lemma B.1)

Lemma B.1 is stated for an **arbitrary compact metric space** `K`. Its hypotheses are that the
`phi`-derivatives of `Psi` up to order 4 and of `a` up to order 2 are jointly continuous on
`K x T^m`, together with (i) to (iii) at every point. Its proof shows that the `O(1/T)` constant
depends only on `m`, `sigma_min`, `B_Psi`, `B_a`, `eps` and `eta`, where `eps` is fixed by
`sigma_min` and `B_Psi`, and `eta` comes from compactness of `{||phi|| >= eps} x K` and (iii). So the
choice `K = P x K_0` is allowed as it stands. All of these are suprema or infima over a compact set
of jointly continuous functions:

- `B_Psi` and `B_a` are suprema of `phi`-derivatives of `Psi = alpha_1 g(z') + sum alpha_i z_i` and
  `chi = b(z') prod z_i` at `z_i = theta_i(alpha; Q) e^{i phi_i}`. These are rational functions of
  `(z', entries of A_F, mu_F)`, and their denominator `det(Z' - A')` does not vanish at these
  points (Lemma A.2 with `s' = theta'`, which is allowed by (A.3)). With `theta'` jointly continuous
  (Lemma U1), every `phi`-derivative is jointly continuous on `P x K_0 x T^{k-1}`. The note's radius
  margin `delta_0` (the minimum of `-varrho(A' - diag theta')/2`) gives the same conclusion. Its
  inequality `2 delta_0 <= min theta_i` holds automatically, since a Perron root dominates the
  diagonal entries. So the margin is correct but not needed. See Section 5 item 6.
- `sigma_min`: `J = Theta' B^T Sigma_alpha B Theta'` is continuous and positive definite on the
  compact set, so its least eigenvalue has a positive minimum.
- `eta`: the bound `Re Psi(alpha, phi) <= Psi(alpha, 0) - sum_{i>=2} alpha_i theta_i (1 - cos phi_i)`
  in the proof of Theorem 4.4 is strict for `phi != 0`. The lemma's own compactness step then gives a
  uniform `eta`. The note's Section 5 says this correctly.
- The conversion from `a(alpha, 0) + O(1/T)` to `a(alpha, 0)(1 + O(1/T))` needs
  `chi(alpha, 0) = (mu.r_alpha)(l_alpha.1)/alpha_1` to be bounded below. This holds on the class,
  since `mu_i >= mu_*` and the eigenvectors are positive and continuous.

So Lemma U2 is proved.

### 2.3 Joint regularity (Lemma U1)

Steps 1 to 4 of the proof of Proposition 4.2(a) run with `Q` as an extra variable: the Perron root
is simple, the Hessian of `Lambda_0` is positive definite (Lemma A.1), and the implicit function
theorem applies to `(beta, alpha', Q)`. Strict convexity makes the solution `beta(alpha, Q)` unique,
so the local analytic branches agree. One point the note does not state, which costs nothing: the
reversible class has empty interior in `R^{d x d}`. "Real-analytic on `C(G; R, b)`" should be read
as the restriction of a map that is analytic on the open set of all `Q` with an irreducible `A_F`.
Only continuity is used.

### 2.4 Transfer (Lemma U3) and the single-word lower bound

The note replaces the lower bound on `H(T alpha)` in Step 3 of the proof of Lemma 4.5, which the
paper takes from Theorem 4.4, by one run word `c^0`. The word walks along the edges of `G` inside
`F`, visits every state, and has `M_0 <= k^2` letters. Its weight is at least
`mu_* (b^2/R)^{M_0 - 1}`, and `prod_i (T alpha_i)^{m_i - 1}/(m_i - 1)! >= eps_0^{M_0 - k} T^{M_0 - k}
/ prod (m_i - 1)!` for `T >= 1` and `alpha` in `K_0`. Combined with the upper bound (A.6) for
`H_e`, this gives `Upsilon(1) <= log(C/c_0) + e T <alpha, theta(alpha)> <= C' T`. This is
`Upsilon(1) = O(T)`, which is all Step 4 uses. The printed proof gets `(e - 1) T <alpha, theta>` plus
`O(log T)`, and the single word costs the full `e T <alpha, theta>`, but both are `O(T)`.
`b(theta'(alpha))` and `theta(alpha)` are continuous on the compact set. Steps 2 and 4 use only
`q_max <= R`, `h q_max <= 1/2`, `T^2/N <= 1` and `n_min >= eps_0 N`. The single-word bound is
uniform, and Lemma U3 is proved.

### 2.5 Face maxima (Proposition U4)

- *Ball.* `J(alpha; p) = I_F - v.alpha - lambda_F(v)` has Hessian `Sigma_alpha^{-1}` in the
  coordinates `alpha'`, since `v.alpha` is affine in `alpha'`. Its gradient vanishes at the interior
  minimizer. The bounds `sigma_*`, `sigma^*`, `B_1`, `B_2` and `B_3` are extrema of continuous
  functions on `P x K_0`. Taking `rho_0 <= eps_0` keeps the ball inside `K_0`: a move of `|x| <=
  rho_0` changes `alpha_1` by at most `sqrt(k - 1) rho_0 <= k eps_0`, and `alpha*_i >= 2 k eps_0`.
  Correct. (The Taylor constant needs a dimensional factor if `B_3` is an entrywise bound. See
  Section 5 item 5.)
- *Outside the ball, and the finite cover of radii.* This was the step the brief singled out. The
  printed proof covers `Delta_F \ U°` for one chain. The note covers the compact set
  `Y = {(p, beta) : |beta' - alpha*'_F(v; p)| >= rho_0}`, which is closed because `alpha*` is
  continuous. `J` is lower semicontinuous on `Y`, as a supremum of jointly continuous functions minus
  a continuous one, and it is positive there by Proposition 3.2(a) and (d) for `Q_F + diag v`. So it
  is at least `3 eta` on `Y`. For fixed `u > 0` the map
  `(p, beta) -> <q - v - A_F(p)u/u, beta> - lambda_F(v; p)` is continuous, so each strict inequality
  `> 2 eta` persists on a neighbourhood with the **same** `u`, and finitely many `u_j` suffice. Then
  `theta_j(p) = A_F(p) u_j/u_j` lies in `V_F(p)` for every `p`, and it is continuous. The constant
  `C_theta = max(e^{k/2} b(theta') prod theta_i, 2 q_max max theta_i)` of Lemma 3.3 is continuous
  along `theta_j(p)`, because `varrho(A' - diag theta_j') < 0` strictly by (A.3) and `b` is rational
  with a nonvanishing denominator there. So the cover is uniform over the class. Correct. This is
  the cleanest part of the note.
- *Inside the ball.* Lemmas U2 and U3 with `K = U`, where `U` is contained in `K_0`. Correct.
- *Lattice point.* It exists once `N alpha*_i > 1` for all `i`, so `N >= 1/(2k eps_0)` is enough.
  Uniform.
- *Bounded `T`, `T_2`, `T_3`.* The joint continuity and positivity of `f^v_T` on
  `[1, T_2] x P x K_0` hold, since `W(m) <= k^M R^{M-1}` gives locally uniform convergence and the
  word `c^0` gives positivity. On the design rectangle `T >= L/(4R)`, so this part is not needed for
  large `N` anyway.

Proposition U4 is proved.

### 2.6 Thresholds and the common onset

On the rectangle `T = tau L` with `tau` in `[1/(4R), U]`. The conditions `h q_max <= 1/2`,
`T <= N^{1/3}`, `T^2/N <= 1` and `1/T + T^2/N <= 5R/L` each say that `N` is large in terms of
`(R, U)` alone. The lattice threshold depends on `eps_0`. `T_2`, `T_3`, `C_4` and the `N_0` of
Lemma U5 depend on the uniform constants. The C-I3 threshold depends on `(d, b/R)`. All are
functions of `(G, R, b, mu_*)`, so the common onset is proved, subject to the C-I3 dependence in
part (d).

### 2.7 The finite-`N` suppression (Lemma U5), and a re-derivation of its input

For a connected face `G` of size at least 2, Lemma 3.3 is applied to the controlled atom with the
Perron tilt `theta = q - v - lambda_G(v) 1`. It lies in `V_G(p)`, because
`A_G - diag theta = Q_G + diag v + lambda_G(v) I` has Perron root 0. It is positive by (A.3) and
continuous in `p`. This gives `M_G <= C N^{-Phi_{tau,v}(G)} T^{|G|-1}` with uniform `C`. The
retained faces have the matching lower bounds from U4 and the exact singleton atom. Disconnected
faces have probability 0, and suppressed singletons are exact.

The score gaps are cited from C-I1. I checked them, because the note only says "uniform by
inspection":

- *Mixed face* `F = F_r cup F_s`, with `F_r` a nonempty subset of `{i, j}` and `F_s` a nonempty set
  of suppressed states. The block `S_{F_s} + M I` is at least `M I` (S is positive semidefinite),
  the coupling block has norm at most `||S|| <= R`, and the retained block's least eigenvalue
  satisfies `e <= max(q_i - delta, q_j) <= 4R`. The Schur bound gives
  `lambda_F(v) >= e - R^2/(M - 4R) = e - 1/(4U)`. So
  `Phi(F) - Phi(F_r) >= |F_s| - tau/(4U) >= 1 - 1/4 = 3/4`, since `tau <= U`. If `F_r` is a nonedge
  pair, its matrix is block diagonal and the comparison is with the better singleton, with an extra
  `+1`.
- *Wholly suppressed face.* `lambda_F(v) >= M`, so `Phi(F) - Phi({i}) >= tau(M - q_i - 3R)
  >= (1/(4R)) 4UR^2 = UR >= 8`.
- *Pair against the singletons at `tau_0`.* By Weyl, `lambda_{ij}(v) >= min(q_i - delta, q_j)
  - sqrt(w_ij)`, so `Phi(pair) - min Phi(singletons) >= 1 - tau_0 R = 1/2`.
- *`{j}` against `{i}` at `delta = H`.* `tau(q_j - q_i + 2R) >= tau R >= 1/4`.

All four gaps are explicit and hold with no limit taken, so they are uniform. Lemma U5 is proved,
given that C-I1's design constants are the ones stated.

## 3. Claim (iii): the expansions, recomputed

### 3.1 The crossing equation

At `delta = H`: `log M_{{i}} = log mu_i + (N - 1) log(1 - h q_i) + T H
= log mu_i - T(q_i - H) + O(T^2/N)`. By (4.3) with `k = 2` for the controlled atom:
`log M_{{i,j}} = -L + (1/2) log T + log K_ij(v) - T lambda_ij(v) + O(1/T + T^2/N)`. Subtracting,

    D_N(T) = -L + delta' T + (1/2) log T + log(K_ij(v)/mu_i) + O(1/L),
    delta' = (q_i - H) - lambda_ij(v) = 1/t_ij .

I checked `1/delta' = t_ij`. With `a = q_i - H` and `c = q_j`, `lambda_ij(v) = (a + c - sqrt((a - c)^2
+ 4w))/2`, so `delta' = ((a - c) + sqrt((a - c)^2 + 4w))/2`. Since `a - c = Delta_ij - H`, this is
`t_ij = (sqrt((H - Delta)^2 + 4w) + H - Delta)/(2w)`, which is the C-I1 formula.

### 3.2 Solving

Put `kappa = log(K_ij(v)/mu_i)` and let `T°` solve `T°/t + (1/2) log T° = L - kappa`. Then
`T° = t[L - kappa - (1/2) log T°]`. Since `T° = tL(1 + O(log L/L))`,
`log T° = log L + log t + O(log L/L)`, and

    tau° = T°/L = t (1 - log L/(2L)) - t[(1/2) log t + kappa]/L + O(log L/L^2).

So `c_ij = -t_ij[(1/2) log t_ij + log(K_ij(v)/mu_i)]`. This matches the note, Theorem 4.7(iii) with
`Delta = 1` and `delta = delta'` (where `b_FG = -(1/2) log t - kappa`). It does **not** match the
heuristic quoted in `00_targets.md` from the Downloads derivations,
`T(lambda_i - lambda_ij) = log N - (1/2) log T + log(K_ij/K_i)`. That display has the wrong sign on
the amplitude term. The correct balance is
`T(lambda_i - lambda_ij) = L - (1/2) log T - log(K_ij/mu_i)`: a larger pair amplitude makes the pair
enter earlier. The note uses the correct sign. The target file and any plan text that copies the
heuristic should be corrected.

- **The sign.** The correction is negative: `-t log L/(2L)`. The `T^{1/2}` Gaussian factor favours
  the pair, so the pair enters earlier than `t_ij` at finite `N`.
- **The 1/2** comes from `(k - 1)/2` with `k = 2`.
- The next term is genuinely `O(log L/L^2)` in `tau`, not `O(1/L^2)`. Its leading part is
  `(t/2)[(1/2) log(tL) + kappa]/L^2`, which grows like `(t/4) log L/L^2`.

`T° = tL + O(log L)` is uniform because `kappa` is bounded on the class (`K_ij(v)` is continuous and
positive, `mu_i >= mu_*`), `t` lies in `[1/R, U/2)`, and `delta' >= 2/U`. The window statement:
`D_N < 0` for `T <= T° - CU/(2L)` and `D_N > 0` for `T >= T° + CU/(2L)`, so
`tau^+_N - tau^-_N = O(1/L^2)`. The note states `C_6/L`, which is weaker than what it proves.

I recomputed `t`, `K_12(v)` (by both Definition 4.1 and Proposition 4.2(b)) and `c` for the note's
six two-state chains. All agree with its table to four digits: for example `(1, 1)` gives
`6.1623, 2.9528, -16.5466`.

### 3.3 The singleton switch

On the retained pair `(i, 1)` at `tau_0` the two singleton atoms are exact, and
`log M_{{i}} - log M_{{1}} = log(mu_i/mu_1) + (N - 1)[log(1 - h q_i) - log(1 - h q_1)] + T delta`.
This is **exactly affine in `delta`** with slope `T`. So the switch is unique, there is no window,
and

    x_{i,N} = q_i - q_1 - log(mu_i/mu_1)/(tau_0 L) + O(1/N + L/N).

This is the note's U6(c), with the error `O(L/N)`. Section 1 of the note says `O(N^{-1/2})`, which
is true but weaker and inconsistent (Section 5 item 4). The note does not say that the difference is
exactly affine. Saying so would strengthen (c) at no cost.

### 3.4 Recovery rates

`x_{i,N} - x_i = O(log(1/mu_*)/L)` and `t_{ij,N} - t_ij = -t log L/(2L) + O(1/L)`. After dividing
by `1 - log L/(2L)`, the error is `t + c/L + O(log L/L^2) - t = O(1/L)`. Through C-I3 (if it holds
as stated) this gives `O(log L/L)` and `O(1/L)` for `||hat Q_N - Q||_2`. Correct given C-I3.

### 3.5 The counterexample over all starts

Two-state rate one, `tau = 1/4`, `v = (0, 1)`: `M_{{1}} = mu_1(1 - h)^{N-1}` and
`M_{{2}} = mu_2(1 - h)^{N-1} e^{T}`. Their ratio is `M_{{1}}/M_{{2}} = (mu_1/mu_2) N^{-1/4}`, up to
the exact factor that cancels. With `mu_2 = 1/(1 + 2N^{1/4})` this is exactly 2. The pair has
`Phi = 1 + (1 - sqrt 5)/8 = 0.845 > 0 = Phi({2})`, so it is not involved. In the language of
(c), the switch in `v_2` sits at `log(mu_1/mu_2)/(tau L) = 1 + 4 log 2/L > 1`. The note's
explanation, that this is the first-order start term made `Theta(1)` by `log(1/mu_2) ~ L/4`, is
right. It is precisely the loss of the bound `|log mu_i| <= log(1/mu_*)`.

## 4. Things I looked for and did not find

- No step uses `T` beyond `N^{1/3}`, and the rectangle has `T <= U log N`.
- No derivative of a remainder is taken: the crossing is located through the values of `D_N`, as
  in Theorem 4.7.
- The definition of `t_{ij,N}` through `tau^-_N` and `tau^+_N` contains the target's "smallest
  `tau` at which `{i,j}` is the maximizing support". That `tau` lies in `[tau^-_N, tau^+_N]`, so no
  uniqueness of the zero of `D_N` is needed.
- The field set includes `v_k = -M` with `M = 4R + 4UR^2`, which is large. All constants stay
  continuous because `alpha*_F(v)` is positive on every connected face for every bounded `v`. For
  mixed faces, `alpha*` puts small but positive mass on suppressed states. U4 is only applied to
  `{i, j}`, and mixed faces enter only through Lemma 3.3, so the small mass costs nothing.
- `T` is not a parameter of the compact set. Lemma B.1 is uniform in `T >= 1`, so this is legitimate.

## 5. Gaps, ranked by severity

1. **(Moderate; named input) Part (d) rests on C-I3.** The stability bound
   `||hat Q - Q||_2 <= C(d, b/R) R eps`, with its admissibility threshold, is a research-note result
   (outline Section 3). It is not proved in the paper or in the note. I did not audit it. Parts
   (a) to (c) do not use it. Lemma U5 cites C-I1's suppression lemma. I re-derived its gaps in
   Section 2.7, so that dependence is discharged, but the paper must print the derivation, because
   the note only cites it.
2. **(Minor; unproved remark) The `mu_{*,N}` extension.** The remark after U6 claims the theorem
   for `log(1/mu_{*,N}) = o(L)` with the rate `O(log(1/mu_{*,N})/L)`. The note's proof bounds
   `chi(alpha, 0)` below and the single word through `mu_*`, so compactness does not give this.
   *Repair:* `P_N(n)`, `H`, `f_T`, `b` and `C_F` are all linear in `mu`, with nonnegative
   coefficients:
   `P_N(n) = sum_i mu_i P^{(i)}_N(n)`. The local law and the transfer hold for each start
   `e_i`, `i in F`, with constants uniform over the class (same proofs, with `mu = e_i`). A
   nonnegative combination of expansions with uniform relative errors has the same relative error.
   Also `nabla log(mu.r_alpha)` is bounded by `max_i |nabla r_{alpha,i}|/r_{alpha,i}`, uniformly in
   `mu`. So U2, U3 and U4 hold uniformly over **all** starts with `mu(F) > 0`, and `mu` enters only
   through `kappa = log(K_ij/mu_i)` and `log(mu_i/mu_1)`. Then (b) reads
   `t_{ij,N} = t(1 - log L/(2L)) + c_ij/L + O((log L + |kappa|)/L^2)`, with `|c_ij| = O(1 + |kappa|)`.
   This repairs the remark, but as written it is unproved. (I checked the three places where the
   start enters: the amplitude, the Taylor bounds for `log C_F`, and the ratio of the Lemma 3.3
   constant `b(theta')` to `K_F`. All three are ratios of nonnegative linear forms in `mu_F` with
   coefficients bounded above and below on the class. I have not written out every line.)
3. **(Minor; constant slip) `E_4` in Proposition U4.**
   `(1 - h q_i)^{N-1} = e^{-T q_i} e^{h q_i + O(T^2/N)}`, so
   `|E_4| <= e^{hR} - 1 + R^2 T^2/N`, not `R^2 T^2/N`. For `T >= 1` this is at most
   `2(R + R^2) T^2/N`. No consequence.
4. **(Minor; inconsistency) Singleton switch error.** Section 1 says `O(1/N^{1/2})` and U6(c) says
   `O(L/N)`. The second is correct (Section 3.3). Harmonize, and add the observation that the
   difference is exactly affine in `delta`.
5. **(Cosmetic) Taylor constants in U4.** With `B_3` a bound on the entries of the third derivative,
   the cubic remainder carries a factor of order `(k - 1)^{3/2}`. Define `B_3` as the operator-norm
   bound of the third derivative, or adjust `rho_0`.
6. **(Cosmetic) Radius margin.** The margin `delta_0` is correct but not needed. Joint continuity of
   the `phi`-derivatives follows because `g` and `b` are rational in `(z', A_F, mu)` with
   `det(Z' - A') != 0` on the torus of radii `theta'`. Either argument can be printed.
7. **(Cosmetic) Strength of (a).** The proof gives `tau^+_N - tau^-_N = O(1/L^2)`, and U6(a)
   states `O(1/L)`.
8. **(Minor; outside the note) Sign in the target contract.** `00_targets.md` (5a)(iv) quotes
   `T(lambda_i - lambda_ij) = log N - (1/2) log T + log(K_ij/K_i)`. The amplitude term has the
   wrong sign (Section 3.2). The note itself is correct.

There is no gap in the uniformity mechanism: the Laplace parameter space, the derivative bounds,
the off-saddle gap, the cover of radii, the single-word transfer bound, the thresholds and the
common onset.

## 6. The cheapest numerical check, and its result

**Design.** A failure of class-uniformity would show as a class member, typically at a corner, whose
normalized remainder `L^2 (t_{ij,N} - t_pred)/log L` grows with `N` or is much larger than the
others. The note's own check uses conservative two-state chains. It never exercises a **killed**
pair face (one whose exit diagonal includes leakage out of the face), which is the situation of every
retained pair in a chain with `d >= 3`. The cheapest check that does is the three-state path
`1 - 2 - 3` in the class `R = 4`, `b = 1`, with retained pair `(1, 2)` and field
`v = (H, 0, -M)`, `H = 8`. The face `{1, 2}` then leaks through `q_23`. The script computes the exact
controlled maxima of `{1}`, `{2}` and `{1, 2}` by the run expansion in log space. The pair maximum is
taken by a grid followed by ternary search, with a run-count truncation that is checked by doubling.
The smallest `tau` at which the pair wins is found by a sign scan (asserting exactly one sign change)
and bisection, and compared with `t(1 - log L/(2L)) + c/L`. `K_12(v)` is computed from Definition 4.1
directly. Chains: the symmetric chain, the `w_12 = b^2` chain, `||S||`-saturating corners found by
random search for the largest and the smallest `t_12` in the class, and starts at `mu_* = 0.05` on
state 1, on state 2 and on state 3. Faces that contain state 3 are not computed (see the caveat
below).

**Result** (`py -I pair_entry_uniform.py`, 142 s). `rem = t_N - t_pred`:

| chain (`q12, q21, q23, q32`; `mu`) | `t_12` | `c_12` | `L^2 rem` at `N = 10^4, 10^6, 10^8` | `L^2 rem/log L` at the same `N` |
|---|---:|---:|---|---|
| sym (1, 1, 1, 1; uniform) | 9.110 | -30.68 | 24.33, 21.08, 21.17 | 10.96, 8.03, 7.27 |
| weak12 (0.5, 2, 0.5, 2; uniform) | 10.099 | -36.29 | 30.07, 25.03, 24.95 | 13.54, 9.53, 8.57 |
| strong (1.4, 1.4, 1, 1; uniform) | 4.700 | -13.15 | 9.86, 9.32, 9.49 | 4.44, 3.55, 3.26 |
| sym; `mu = (.05, .05, .90)` | 9.110 | -30.68 | identical to sym | identical |
| weak12; `mu = (.90, .05, .05)` | 10.099 | -34.57 | 27.48, 22.79, 22.90 | 12.38, 8.68, 7.86 |
| weak12; `mu = (.05, .90, .05)` | 10.099 | -49.80 | 44.11, 37.65, 36.36 | 19.87, 14.34, 12.48 |
| corner, largest `t` (0.518, 2.085, 0.877, 1.387; uniform) | 9.756 | -35.13 | 28.65, 24.20, 24.15 | 12.91, 9.22, 8.29 |
| corner, smallest `t` (2.605, 0.856, 0.640, 1.849; uniform) | 3.229 | -7.50 | 5.37, 5.64, 5.81 | 2.42, 2.15, 2.00 |
| corner largest `t`; `mu = (.05, .90, .05)` | 9.756 | -48.17 | 42.38, 36.41, 35.17 | 19.09, 13.86, 12.07 |

Reading. On every class member, including the `||S||_2 = R` corners and the starts at `mu_*`,
`L^2 rem` is bounded and does not grow from `N = 10^4` to `10^8`. The supremum over the sample falls
from 44 to 36. So the killed-pair version of U6(b) behaves as claimed, with no sign of a blow-up
anywhere in the class. The constant is largest when `mu_1 = mu_*` and `t_12` is large. This matches
the next-order term I derived in Section 3.2, `(t/2)[(1/2) log(tL) + kappa]/L^2`: for weak12 with
`mu_1 = 0.05` it predicts about 32 against the observed 36. It also confirms Section 5 item 2: the
hidden constant grows linearly in `|kappa| = |log(K_12/mu_1)|`, so it is bounded on `M(mu_*)` but
not over all starts. The row "sym with `mu = (.05, .05, .90)`" equals the uniform row exactly, as it
must: the three competing atoms are linear in `(mu_1, mu_2)` and are scaled by the same factor.
`c_12/L` lies between `-0.4` and `-2.7` at `N = 10^8` (`L = 18.4`), far larger than the remainder
(`rem` is at most `0.11`), so the note is right
that the correction `t_{ij,N}/(1 - log L/(2L))` improves the rate but leaves an `O(1/L)` error
`c_ij/L` that depends on the unknown chain.

Caveat. Neither this check nor the note's checks the finite-`N` suppression of faces that contain a
suppressed state, because exact three-state face maxima at `N >= 10^4` are expensive. With
`M = 4R + 4UR^2 = 2064` those faces are smaller by factors that no finite computation could make
interesting. The evidence for Lemma U5 is the explicit gap derivation in Section 2.7.

## 7. Verdict

**Conditional on a named input.** Theorem U6(a) to (c) are proved as written on the compact class
`C(G; R, b) x M(mu_*)` with the C-I1 design, apart from the minor slips in Section 5 items 3 to 7.
The suppression input from C-I1 is checked in Section 2.7 and has to be printed in the paper.
Theorem U6(d) is conditional on the stability bound C-I3. The remark extending the theorem to
`mu_* = mu_{*,N}` with `log(1/mu_{*,N}) = o(log N)` is unproved as written, and Section 5 item 2
gives the missing argument (linearity in `mu` of every object in the local theory). The smallest
missing implication for the full statement as the note states it is therefore: "C-I3 holds with a
constant and threshold that depend only on `(d, b/R)`". For the remark, it is "the local law and the
transfer hold with relative errors uniform over all starts with `mu(F) > 0`", which the linearity
argument supplies.
