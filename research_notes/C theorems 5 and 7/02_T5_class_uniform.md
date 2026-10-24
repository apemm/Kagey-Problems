# Route T5-B. Theorem 5, class-uniform finite-horizon recovery

Base checkpoint: commit `6add913`. Date: October 24, 2026.

Inputs read in full: `paperC/sec_model.tex` (setting, run expansion, continuum density),
`paperC/sec_firstorder.tex` lines 164 to 480 (Proposition 3.2 on the rate, Lemma 3.3, Theorem 3.4),
`paperC/sec_secondorder.tex` lines 1 to 520 (Definition 4.1, Proposition 4.2, Theorem 4.4,
Lemma 4.5, Theorem 4.6, Theorem 4.7, Theorem 4.8 with their proofs), `paperC/app_torus.tex`
(Lemma A.1, proof of Proposition 4.2(a), Lemma A.2, proofs of Lemma 3.3, Theorem 4.4, Lemma 4.5 and
Theorem 3.4(ii)), `paperC/app_laplace.tex` (Lemma B.1 and its proof), and Sections 2B and 2C of
`research_notes/Occupation novelty and compact advances/12_Good_original_closure.md`. The design
constants and the counterexample over all starts are quoted from
`11_C_ready_to_draft_outline.md` Sections 1, 3 and 5. The numbering of statements is that of the
build of October 23, 2026 (labels in brackets).

Scripts: `02_T5_uniformity_check.py`, output `02_T5_uniformity_output.txt` (Section 7).

## 1. Result in one paragraph

The class-uniform statement (5b) holds, and no new estimate is needed. Two exact facts remove the
field from every constant of the local theory, and a compactness argument removes the chain and
the start. First, the controlled atom `Pr_mu(n) e^{Tv.n/N}` equals `P_N(n) e^{h v.n}` with
`h = T/N`, so its ratio to the continuum density of the killed matrix with diagonal `q - v` is
exactly the ratio of Lemma 4.5 for the uncontrolled chain, and its local law is the local law of
Theorem 4.4 with the rate `I_F - v.alpha` and the same constant `C_F(alpha)`, because the
optimal tilt `r_alpha` does not depend on the diagonal of `Q_F`. Second, every constant and every
threshold in the proofs of Lemma 3.3, Theorem 4.4, Lemma 4.5 and Theorem 4.6 is either a continuous
function of the parameter `p = (Q, mu, v)` or the outcome of a finite covering of a compact set,
and in the second case the covering can be taken over the compact parameter set as well. The
parameter set of the theorem,

    P = { (Q, mu) : Q reversible on the given connected graph G, ||S||_2 <= R, sqrt(w_ij) >= b on
          the edges, min_i mu_i >= mu_* } x { v in the protected design, |delta| <= 3R } ,

is compact, so all constants are uniform on it. The crossing argument of Theorem 4.7 then gives
`t_{ij,N} = t_ij (1 - log log N/(2 log N)) + c_ij/log N + O(log log N/(log N)^2)` with an explicit
`c_ij` and a uniform remainder, and the singleton switches satisfy
`x_{i,N} = x_i - log(mu_i/mu_1)/(tau_0 log N) + O(1/N^{1/2})`. The two-state counterexample over
all starts is the term `log(mu_i/mu_1)/(tau_0 log N)` evaluated at a start whose mass is a power
of `N`, that is, the failure of the bound `|log mu_i| <= log(1/mu_*)` when `mu_*` is not fixed.

Sections 2 and 3 record the exact facts and the table of constants. Section 4 writes the
uniform statements and their proofs in the form intended for the paper. Section 5 treats the
delicate steps named in the brief, Section 6 the counterexample and the thresholds, and Section 7
the numerical check.

## 2. Two exact facts about the controlled atom

Fix a face `F` with `k >= 2` states, a field `v` in `R^F`, and write `h = T/N`.

**Fact 1 (the field factors out of the transfer).** For `supp n = F` and `alpha = n/N`,

    Pr_mu(n) e^{T v.n/N} = P_N(n) e^{h v.n} = P_N(n) e^{T v.alpha} .

The continuum density of Lemma 2.3 [lem:continuum] for the killed matrix with diagonal `q - v`
is `f^v_T(alpha) = T^{k-1} e^{-T <q - v, alpha>} H(T alpha) = e^{T v.alpha} f_T(alpha)`, with the
same `H`, since `H` only involves the off-diagonal rates and the start. Hence

    Pr_mu(n) e^{T v.n/N} / ( N^{-(k-1)} f^v_T(n/N) ) = P_N(n) / ( N^{-(k-1)} f_T(n/N) ) ,

exactly. So Lemma 4.5 [lem:discrete] holds for the controlled atom with the same constants, and
the field does not enter them at all.

**Fact 2 (the field does not change the tilt or the constant).** The optimal vector `r_alpha` of
Definition 4.1 [def:tilt] maximizes `u -> <q - A_F u/u, alpha>`, and `q` enters this function only
through the additive term `<q, alpha>`. So `r_alpha`, `l_alpha`, `theta(alpha)`, `Sigma_alpha`
and `C_F(alpha)` are the same for the diagonal `q - v` as for `q`, while the rate becomes
`I_F(alpha) - v.alpha`. The torus representation of Lemma A.2 [lem:torus] involves only `A_F`,
`mu_F` and the radii `theta'(alpha)`, so the proof of Theorem 4.4 [thm:local] goes through word
for word and gives, uniformly for `alpha` in a compact subset of the open face and `T >= 1`,

    f^v_T(alpha) = T^{(k-1)/2} C_F(alpha) e^{-T (I_F(alpha) - v.alpha)} (1 + O(1/T)) ,

where the implied constant is the constant of Theorem 4.4 and does not depend on `v`. The
whole-face bound of Lemma 3.3 [lem:upper] multiplied by `e^{h v.n}` reads

    Pr_mu(n) e^{T v.n/N} <= C_theta h^{k-1} exp( -h <n, q - v - theta> + C_theta h^2 |n| )

for every `theta` in `V_F`, with the constant of Lemma 3.3.

Consequently the field enters the face maximum only through three continuous quantities, the
minimizer `alpha*_F(v)` of `I_F - v.alpha` on the closed face, its value `lambda_F(v)`, and
`K_F(v) = C_F(alpha*_F(v))`. By Proposition 3.2 [prop:rate] applied to the matrix `Q_F + diag v`
(its proof uses only that `A_F` is irreducible and that the diagonal is a fixed vector), the
minimizer is unique, it is the quasi-ergodic law `l circ r` of `Q_F + diag v`, and
`lambda_F(v) = -varrho(Q_F + diag v)`. These three maps are real-analytic in `(Q, v)` on the open
set where `A_F` is irreducible, by the implicit function theorem for the simple Perron root.

## 3. The constants, what they depend on, and why each one is uniform

Notation. `p = (Q, mu, v)` runs over the compact set `P` of Section 1, `F` over the finitely many
connected faces, and `K_0 = {alpha : alpha_i >= eps_0 for all i in F}`, where `eps_0 > 0` is
chosen so small that `min_i alpha*_{F,i}(v) >= 2 k eps_0` for every `p` in `P` and every connected
`F` (possible since `alpha*_F(v)` is continuous and positive on the compact set `P`). The word
"continuous" below means continuous as a function of `p` on `P`, and "covering" means that the
constant comes from a finite subcover of a compact set that can be taken to include `p`.

| Where | Constant or threshold | Depends on | Uniform because |
|---|---|---|---|
| Lemma 2.3, (2.2) [eq:vertexmax] | relative error `T^2/N` of the singleton atom, constant `q_i^2` | `q_i` | `q_i <= R` |
| Lemma 3.3 [lem:upper] | `C_theta = max(e^{k/2} b(theta') prod theta_i, 2 q_max max theta_i)` | `theta`, `A_F`, `mu` | for `theta = theta(p)` continuous with `theta(p) in V_F(p)`, the radii satisfy `varrho(A' - diag theta') < 0` strictly, so `b(theta'; A_F, mu)` is continuous; hence `C_theta` is continuous |
| Lemma A.1 [lem:perron], Prop. 4.2(a) | analyticity of `theta(alpha)`, `r_alpha`, `l_alpha`, `Sigma_alpha` | `(alpha, A_F)` | the Perron root of an irreducible Metzler matrix is simple, so the implicit and inverse function theorems apply jointly in `(alpha, A_F)`; see Lemma U1 below |
| Lemma A.2 [lem:torus], regularity step of the proof of Thm 4.4 | radius margin `delta` with `varrho(A' - diag(theta' - delta 1)) < 0` | `(alpha, A_F)` | the gap `-varrho(A' - diag theta'(alpha))` is continuous and positive, so it has a positive minimum on `P x K_0`; covering |
| Lemma B.1 [lem:laplace] | `B_Psi`, `B_a`, `sigma_min`, `eps`, `eta`, hence the `O(1/T)` of Thm 4.4 | the compact parameter space of the lemma | the lemma is stated for an abstract compact metric space; take it to be `P x K_0` (Lemma U2) |
| Proof of Thm 4.4, last step | lower bound for `chi(alpha, 0) = (mu.r_alpha)(l_alpha.1)/alpha_1` | `(alpha, A_F, mu)` | continuous and positive on `P x K_0`, since `mu_i >= mu_*` and `r_alpha, l_alpha > 0` |
| Proof of Lemma 4.5, Step 3 | `C_K` in `Upsilon(1) <= C_K T`, through an upper bound for `H_e` and a lower bound for `H` | `theta(alpha)`, `b(theta')`, the local law, or one positive run word | the upper bound is continuous; the lower bound is either the uniform local law for `T >= T_1` and joint continuity and positivity of `f_T` on `[1, T_1] x P x K_0` for small `T`, or the single-word bound `W(m^0) prod eps_0^{m^0_i - 1}/(m^0_i - 1)! T^{M_0 - k}` with `W(m^0) >= mu_* (b^2/R)^{M_0 - 1}` |
| Proof of Lemma 4.5, Step 4 | `eps_K = min_{K_0} min_i alpha_i` | `K_0` | equals `eps_0` |
| Proof of Thm 4.6, the ball `U` | `rho_0`, `c_U`, `C_U`, `C_1`, `C_3` | second and third derivatives of `I_F - v.alpha` and of `log C_F` near `alpha*_F(v)` | `nabla^2 I_F = Sigma_alpha^{-1}` is continuous and positive definite on `P x K_0`, the third derivatives of `I_F` and the first two of `log C_F` are continuous there; Taylor's theorem with uniform bounds gives one `rho_0` and uniform constants (Lemma U3) |
| Proof of Thm 4.6, outside `U` | `eta` with `I_F - v.alpha >= lambda_F(v) + 3 eta` off the ball | lower semicontinuity of `I_F` and uniqueness of the minimizer | `I_F(beta; Q) - v.beta - lambda_F(v)` is a supremum of continuous functions of `(beta, p)` minus a continuous function, so it is lower semicontinuous on the compact set `{(p, beta) : |beta' - alpha*'_F(v)| >= rho_0}` and positive there, hence bounded below by `3 eta > 0` |
| Proof of Thm 4.6, outside `U` | the finite family `theta_j` and their `C_{theta_j}` | covering of `Delta_F \ U` | cover the compact set of pairs `(p, beta)` instead, with vectors `u_j > 0` and `theta_j(p) = A_F(p) u_j/u_j`, which is continuous in `p` and lies in `V_F(p)`; finitely many `u_j` suffice, and each `C_{theta_j(p)}` is continuous, hence bounded |
| Proof of Thm 4.6, inside `U` | `C_2` in `|E| <= C_2 (1/T + T^2/N)` | Thm 4.4 and Lemma 4.5 with `K = U` | both uniform by the rows above, since `U` is contained in `K_0` |
| Proof of Thm 4.6, lower bound | existence of `n^0` with `|n^0_i - N alpha*_i| < 1`, threshold `N_0` | `min_i alpha*_i` | `N_0 = ceil(1/(k eps_0))` works for all `p` |
| Proof of Thm 4.6, bounded `T` | `T_2`, and bounds for `f_T` on `[1, T_2] x U` | continuity and positivity of `f_T` | `f_T(alpha; Q, mu)` is jointly continuous and positive in `(T, alpha, Q, mu)` (a locally uniformly convergent power series with positive coefficients, some positive by (H)), so bounded above and below on the compact set `[1, T_2] x P x K_0` |
| Proof of Thm 4.6, maximizer | `T_3`, `C_4` | the constants above | uniform |
| Thm 4.6 [thm:facemax] | `K_F(v) = C_F(alpha*_F(v))` bounded above and below | `p` | continuous and positive on `P` |
| Thm 4.7 [thm:crossing] | the `O(1/L)` in (4.4) [eq:crossing] | the `O(1/T + T^2/N)` of (4.3) [eq:logmax] on `[L/(4R), U L]`, and `delta' >= delta_min` | uniform by the rows above; `delta' = lambda_{i}(v) - lambda_{ij}(v)` is continuous and positive on `P` (it equals `1/t_ij` with `t_ij < U/2`), so `delta' >= 2/U` |
| Design (C-I1) | `H = 2R`, `tau_0 = 1/(2R)`, `U = 8R/b^2`, `M = 4R + 4UR^2`, the gaps `3/4` and `1/2`, `t_ij in [1/R, U/2)` | `R`, `b` only | explicit |
| Stability (C-I3) | `C(d, b/R)` and the admissible error size | `d`, `b/R` | explicit |
| Thresholds | `h q_max <= 1/2`, `T <= N^{1/3}`, `T <= N^{1/2}` on the rectangle `T in [L/(4R), U L]` | `R`, `U` | `N >= N_1(R, U)` suffices for all `p` (Section 6) |

The table has no entry that depends on `p` other than through a continuous function or a covering.
This is the whole content of the uniformity claim, and the next section writes it as proofs.

## 4. The uniform statements, written for the paper

Throughout, `G` is a fixed connected graph on `d >= 2` labelled states with `m` edges, and
`0 < b <= R`, `0 < mu_* <= 1/d` are fixed. We write `C(G; R, b)` for the set of reversible
irreducible generators `Q` on `G` with `||S||_2 <= R` and `sqrt(w_ij) >= b` on every edge, where
`S = D_pi^{1/2}(-Q)D_pi^{-1/2}` and `w_ij = q_ij q_ji`, and `M(mu_*)` for the set of starts with
`min_i mu_i >= mu_*`. A field is a vector `v` in `R^d` with `|v_i| <= V` for a fixed `V`. The
design of C-I1 uses `V = M + 3R`. We call `P = C(G; R, b) x M(mu_*) x [-V, V]^d` the parameter set,
and we write `p = (Q, mu, v)` for its points. We say that a bound holds uniformly on `P` if the
constants and the thresholds in it can be chosen as functions of `(G, R, b, mu_*, V)` alone.

**Lemma U0 (the parameter set is compact).** `P` is a compact subset of `R^{d x d} x R^d x R^d`.

*Proof.* The constraint `||S||_2 <= R` bounds every entry of `S`, and `q_i = S_ii`. On an edge,
`q_ij q_ji = w_ij = S_ij^2 >= b^2` and `q_ij <= q_i <= R`, so `q_ij >= b^2/R`. Off the edges
`q_ij = 0`. Reversibility is the closed condition `q_ij q_jk q_ki = q_ik q_kj q_ji` on all triples
(Kolmogorov's criterion) together with the pattern, and the norm constraint is closed because
`S` depends continuously on `Q` through `pi`, which is continuous on the set of irreducible
generators with a fixed pattern. So `C(G; R, b)` is closed and bounded, and the two other factors
are closed and bounded. `qed`

Every `Q` in `C(G; R, b)` has every edge rate at least `b^2/R`, so every connected face `F` is
irreducible for every `Q` in the class, and every face whose induced graph is disconnected has
probability zero by Lemma 2.1(c) [lem:admissible]. In what follows `F` is a connected face with
`k >= 2` states.

**Lemma U1 (joint regularity).** The maps `(alpha, Q) -> theta(alpha)`, `r_alpha` (normalized by
`sum_i r_{alpha,i} = 1`), `l_alpha`, `Sigma_alpha`, `I_F(alpha)` and `C_F(alpha)` are real-analytic
on `Delta_F^o x C(G; R, b)`, jointly in both arguments, and `C_F` is also real-analytic in `mu`.
The maps `(Q, v) -> alpha*_F(v)`, `lambda_F(v)` and `K_F(v)` are real-analytic on
`C(G; R, b) x R^F`.

*Proof.* We repeat the proof of Proposition 4.2(a) with `Q` as an additional variable. For
`(vartheta, Q)` with `A_F` irreducible, `Lambda(vartheta; Q) = varrho(Q_F + diag vartheta)` is a
simple eigenvalue, so by the implicit function theorem applied to the characteristic polynomial
it is real-analytic in `(vartheta, Q)`, and so are its normalized positive eigenvectors. The
Hessian in `vartheta` of `Lambda_0(beta; Q) = Lambda((0, beta); Q)` is positive definite by Lemma
A.1, so the equation `nabla_beta Lambda_0(beta; Q) = alpha'` has, by the implicit function theorem
with the parameter `(alpha', Q)`, a real-analytic solution `beta(alpha, Q)` near every solution.
Steps 3 and 4 of that proof then give `theta`, the eigenvectors, `Sigma_alpha` and `I_F` as
real-analytic functions of `(alpha, Q)`, and `C_F` is a product of these with the linear factor
`mu.r_alpha`. For the last claim, `Q_F + diag v` is an irreducible Metzler matrix, its Perron root
is simple, and `alpha*_F(v) = l circ r` with the normalized Perron vectors. `qed`

**Lemma U2 (uniform local law).** There are `eps_0 > 0`, `C_loc` and, for the compact set
`K_0 = {alpha in Delta_F : alpha_i >= eps_0 for all i}`, the following. For every `p` in `P`,
every `alpha` in `K_0` and every `T >= 1`,

    f^v_T(alpha) = T^{(k-1)/2} C_F(alpha) e^{-T(I_F(alpha) - v.alpha)} (1 + E_1) ,
    |E_1| <= C_loc/T ,

and `min_i alpha*_{F,i}(v) >= 2 k eps_0` for every `p` in `P`.

*Proof.* By Lemma U1 and Lemma U0, `min_i alpha*_{F,i}(v)` is a continuous positive function on
the compact set `P`, so it has a positive minimum, and we take `eps_0` smaller than this minimum
divided by `2k`. By Fact 2 it is enough to prove the claim for `v = 0` with a constant that does
not depend on `p`. We go through the proof of Theorem 4.4 in Appendix A with the compact
parameter space `K = P x K_0` in place of `K_0`. The torus representation (A.4) [eq:A-fT] holds
for every `(p, alpha)` with the radii `theta'(alpha; Q)`. The phase `Psi` and the amplitude `chi`
are built from `g`, `b` and `theta'`, and `g` and `b` are rational functions of `z'` and of the
entries of `A_F` and `mu_F` that are holomorphic in `z'` on `{|z_i| > theta_i - delta}` as soon as
`varrho(A' - diag(theta' - delta 1)) < 0`. The number `-varrho(A' - diag theta'(alpha; Q))` is
continuous and positive on `P x K_0`, by Lemma U1 and the second fact of Appendix A, so it has a
positive minimum `2 delta_0`, and with `delta = delta_0` the `varphi`-derivatives of `Psi` and
`chi` of every order are jointly continuous on `P x K_0 x T^{k-1}`. Hypotheses (i) to (iii) of
Lemma B.1 hold at every point of `P x K_0`, by the pointwise argument of Appendix A. Lemma B.1
with the compact metric space `P x K_0` gives the expansion with a constant depending only on
`k`, `sigma_min`, `B_Psi`, `B_a`, `eps` and `eta`, all of which are now suprema or infima over
`P x K_0 x T^{k-1}`. Finally `chi(alpha, 0) = (mu.r_alpha)(l_alpha.1)/alpha_1` is continuous and
positive on `P x K_0` because `mu_i >= mu_*` and the eigenvectors are positive, so it is bounded
below, and the bracket `chi(alpha, 0) + O(1/T)` is `chi(alpha, 0)(1 + O(1/T))` uniformly. `qed`

**Lemma U3 (uniform transfer).** With `eps_0` and `K_0` as in Lemma U2 there is `C_tr` such that
for every `p` in `P`, every `n` with `supp n = F` and `n/N` in `K_0`, and every `1 <= T <= N^{1/2}`,

    Pr_mu(n) e^{T v.n/N} = N^{-(k-1)} f^v_T(n/N) (1 + E_2) ,     |E_2| <= C_tr T^2/N .

*Proof.* By Fact 1 it is enough to treat `v = 0`. In the proof of Lemma 4.5, Steps 1, 2 and 4
involve only `q_max <= R`, `eps_K = eps_0` and the moment bounds of Step 3. In Step 3 the upper
bound `H_e(T alpha) <= e^{k-1} b(theta') prod_{i >= 2} theta_i e^{e T <alpha, theta>}` has a
constant that is continuous on `P x K_0`. For the lower bound we fix one run word `c^0` that starts
in a state of `F`, visits every state of `F` along edges of `G`, and has `M_0 <= k^2` letters. Its
weight is `W(m^0) >= mu_* (b^2/R)^{M_0 - 1}`, and for `T >= 1` and `alpha` in `K_0`,

    H(T alpha) >= W(m^0) prod_i (T alpha_i)^{m^0_i - 1}/(m^0_i - 1)! >= c_0 T^{M_0 - k} >= c_0 ,

with `c_0 = mu_* (b^2/R)^{M_0 - 1} eps_0^{M_0 - k} prod_i 1/(m^0_i - 1)!`. Dividing the two bounds,
`Upsilon(1) <= log(C/c_0) + e T <alpha, theta> <= C_tr' T` on `P x K_0` for `T >= 1`, since
`<alpha, theta>` is bounded there. The rest of the proof is unchanged. `qed`

This lower bound replaces the use of Theorem 4.4 in Step 3 of the printed proof, as the Good note
already observed, and it makes the uniformity of the transfer independent of the local law.

**Proposition U4 (uniform face maxima for the controlled atom).** Let `M_F(p) = max{Pr_mu(n)
e^{T v.n/N} : supp n = F}`. There are `N_0`, `C_max` and `rho_0 > 0` such that for every `p` in `P`,
every `N >= N_0` and every `1 <= T <= N^{1/3}`,

    M_F(p) = K_F(v) N^{-(k-1)} T^{(k-1)/2} e^{-T lambda_F(v)} (1 + E_3) ,
    |E_3| <= C_max (1/T + T^2/N) ,

every maximizer `hat n` satisfies `|hat n/N - alpha*_F(v)| <= C_max/T`, and for every `n` with
`supp n = F` and `|n'/N - alpha*'_F(v)| >= rho_0`,

    Pr_mu(n) e^{T v.n/N} <= C_max N^{-(k-1)} T^{k-1} e^{-T(lambda_F(v) + 2 eta)}

with a fixed `eta > 0`. For a singleton, exactly,
`M_{{i}}(p) = mu_i (1 - h q_i)^{N-1} e^{T v_i} = mu_i e^{-T(q_i - v_i)} (1 + E_4)` with
`|E_4| <= R^2 T^2/N` for `T <= N^{1/2}`.

*Proof.* We follow the proof of Theorem 4.6 and replace each pointwise choice by a choice on the
compact set `P`. Write `J(alpha; p) = I_F(alpha; Q) - v.alpha - lambda_F(v)`, which is
nonnegative on `Delta_F` and vanishes only at `alpha*_F(v)` by Proposition 3.2(a) for the matrix
`Q_F + diag v`, and write `x = alpha' - alpha*'_F(v)`.

*The ball.* On `P x K_0` the Hessian `nabla^2 J = Sigma_alpha^{-1}` is continuous and positive
definite, so its least eigenvalue has a positive minimum `sigma_*` and its largest eigenvalue a
finite maximum `sigma^*`, the third derivatives of `J` are bounded by some `B_3`, and the first and
second derivatives of `log C_F` are bounded by some `B_1` and `B_2`. All these bounds come from
Lemma U1 and Lemma U0. Take `rho_0 = min(eps_0, 3 sigma_*/(2 B_3))`. For `|x| <= rho_0` the point
`alpha` lies in `K_0` (each coordinate moves by at most `k rho_0 <= k eps_0`, and
`alpha*_i >= 2 k eps_0`), and Taylor's theorem gives

    (sigma_*/4) |x|^2 <= J(alpha; p) <= (sigma^*/2 + B_3 rho_0/6) |x|^2 ,
    |log(C_F(alpha)/K_F(v)) - gamma.x| <= B_2 |x|^2/2 ,

with `gamma = nabla log C_F(alpha*_F(v))`, `|gamma| <= B_1`, and `log C_F` is `B_1`-Lipschitz on
the ball. So the constants `c_U`, `C_U`, `C_1`, `C_3` and `|gamma|` of the printed proof are
uniform on `P`.

*Outside the ball.* The set `Y = {(p, beta) : p in P, beta in Delta_F, |beta' - alpha*'_F(v)| >=
rho_0}` is compact, and `J` is lower semicontinuous on it, because `I_F(beta; Q) =
sup_u <q - A_F u/u, beta>` is a supremum of functions that are jointly continuous in `(beta, Q)`,
and `v.beta + lambda_F(v)` is continuous. A lower semicontinuous positive function on a compact
set has a positive minimum, which we call `3 eta`. For each `(p_0, beta_0)` in `Y` choose
`u_0 > 0` with `<q(p_0) - v_0 - A_F(p_0)u_0/u_0, beta_0> > lambda_F(v_0; Q_0) + 2 eta`. The left
side minus the right side is continuous in `(p, beta)`, so the inequality persists on a
neighbourhood of `(p_0, beta_0)` in `Y` with the same `u_0`. Finitely many neighbourhoods cover
`Y`, with vectors `u_1, ..., u_J`. Put `theta_j(p) = A_F(p) u_j/u_j`. For every `p` this vector
lies in `V_F(p)`, since `u_j` is a positive null vector of `A_F(p) - diag theta_j(p)`, and it is
continuous in `p`. By Fact 2 and Lemma 3.3 with `theta = theta_j(p)`, for `n` with
`(p, n/N)` in `Y` and `j` attaining the maximum,

    Pr_mu(n) e^{T v.n/N} <= C_{theta_j(p)} h^{k-1} e^{-T(lambda_F(v) + 2 eta) + C_{theta_j(p)} T^2/N} .

The constant `C_theta` of Lemma 3.3 is `max(e^{k/2} b(theta') prod_{i >= 2} theta_i,
2 q_max max_i theta_i)`, and for `theta = theta_j(p)` the radii satisfy
`varrho(A' - diag theta') < 0` strictly by (A.3) [eq:A-radii], so `b(theta_j'(p); A_F(p), mu)` is
continuous in `p`. Hence `max_j sup_P C_{theta_j(p)} < infinity`, and with `T^2/N <= 1` this is the
third display of the proposition.

*Inside the ball.* Lemma U2 and Lemma U3 give (4.2) [eq:insideU] with a uniform `C_2`, and the
printed maximization of the concave quadratic uses only `c_U`, `C_1` and `|gamma|`.

*The lower bound, bounded `T`, and the maximizer.* The lattice point `n^0` exists for
`N >= 1/(k eps_0)`. For `1 <= T <= T_2` we need `f_T` bounded above and below on
`[1, T_2] x P x K_0`. The function `(T, alpha, Q, mu) -> H(T alpha)` is a power series in the rates
and in `T alpha` with nonnegative coefficients that converges locally uniformly, so it is
continuous, and it is positive because the word `c^0` of Lemma U3 has positive weight. The factor
`e^{-T <q - v, alpha>}` is continuous and positive. So `f^v_T` has positive upper and lower
bounds on this compact set, and `N^{k-1} X` lies between two positive constants because
`K_F(v)` and `lambda_F(v)` are bounded on `P`. The remaining steps of the printed proof use only
the constants already made uniform, and `T_2`, `T_3`, `C_4` and `N_0` are determined by them. The
singleton statement is (2.2) with `log(1 - x) >= -x - x^2` for `x = h q_i <= 1/2` and
`q_i <= R`. `qed`

**Lemma U5 (finite-horizon suppression).** Let `(i, j)` be a retained pair of the design of C-I1,
with `v_i = delta`, `v_j = 0`, `v_k = -M` otherwise, `|delta| <= 3R`, and `1/(4R) <= tau <= U`.
There are `N_0` and `C_5` such that for every `p` in `P`, every `N >= N_0` and every face
`G notin {{i}, {j}, {i, j}}`,

    M_G(p) <= C_5 N^{-3/4} (log N)^{d} max( M_{{i}}(p), M_{{j}}(p), M_{{i,j}}(p) ) ,

and at `tau = tau_0` the pair satisfies `M_{{i,j}}(p) <= C_5 N^{-1/2} (log N)^{d} max(M_{{i}}, M_{{j}})`.

*Proof.* The suppression lemma of C-I1 gives, for every `p` in `P` and every point of the
rectangle, `Phi_{tau,v}(G) >= min(Phi_{tau,v}({i}), Phi_{tau,v}({j}), Phi_{tau,v}({i,j})) + 3/4`
for the faces `G` in question, and the singleton advantage `1/2` over the pair at `tau_0`. These
are explicit inequalities in `R`, `b`, `M` and the Schur complement, with no limit taken, so they
hold uniformly on `P`. Now `M_G(p) = 0` unless `G` is connected. For connected `G` with at least
two states, the third display of Proposition U4 is not needed. Lemma 3.3 with
`theta = q - v - lambda_G(v) 1`, which lies in `V_G(p)` because `A_G - diag theta = Q_G + diag v +
lambda_G(v) I` has Perron root zero, gives

    M_G(p) <= C_{theta(p)} (T/N)^{|G| - 1} e^{-T lambda_G(v) + C_{theta(p)} T^2/N}
            = N^{-Phi_{tau,v}(G)} T^{|G|-1} e^{O(1)} ,

with `C_{theta(p)}` continuous in `p` by the same argument as in Proposition U4. For a singleton
`G` the atom is exact. For the three retained faces Proposition U4 and the exact singleton atom
give lower bounds `M_F(p) >= c N^{-Phi_{tau,v}(F)}` with `c > 0` uniform, since `T^{(k-1)/2}
K_F(v) e^{O(1/T + T^2/N)}` is bounded below on the rectangle. Combining the two bounds with the
score gaps `3/4` and `1/2` gives the claims with `(log N)^d` absorbing the powers of `T <= U log N`.
`qed`

**Theorem U6 (class-uniform finite-horizon recovery).** Fix `G`, `R`, `b`, `mu_*`, and run the
design of C-I1 at horizon `N`. For a retained pair `(i, j)` and `delta = H` let `W_N(tau)` be the
set of supports of the maximizers of the controlled atom at `tau`, and define

    tau^-_N = sup{ tau in [1/(4R), U] : W_N(tau') = {{i}} for all tau' <= tau } ,
    tau^+_N = inf{ tau in [1/(4R), U] : W_N(tau') = {{i, j}} for all tau' >= tau } ,

and let `t_{ij,N}` be any number in `[tau^-_N, tau^+_N]`. Define `x_{i,N}` in the same way from
the switch of `W_N` between `{1}` and `{i}` as `delta` increases at `tau = tau_0`. Then there are
`N_0` and `C_6` depending only on `(G, R, b, mu_*)` such that for every `(Q, mu)` in
`C(G; R, b) x M(mu_*)` and every `N >= N_0`, with `L = log N`,

    (a)  tau^+_N - tau^-_N <= C_6/L ,
    (b)  | t_{ij,N} - t_ij (1 - log L/(2L)) - c_ij/L | <= C_6 log L/L^2 ,
         c_ij = - t_ij [ (1/2) log t_ij + log( K_{ij}(v)/mu_i ) ] ,   |c_ij| <= C_6 ,
    (c)  | x_{i,N} - x_i + log(mu_i/mu_1)/(tau_0 L) | <= C_6 L/N ,   so   |x_{i,N} - x_i| <= 2R log(1/mu_*)/L + C_6 L/N ,
    (d)  the generator `hat Q_N` reconstructed by C-I1 from `(x_{i,N})` and `(t_{ij,N})` satisfies
         `||hat Q_N - Q||_2 <= C_6 log L/L`, and the one reconstructed from `(x_{i,N})` and
         `(t_{ij,N}/(1 - log L/(2L)))` satisfies `||hat Q_N - Q||_2 <= C_6/L`.

Here `K_{ij}(v)` is `K_F(v)` for `F = {i, j}` at the design field, `t_ij = 1/delta'` with
`delta' = (q_i - H) - lambda_{ij}(v) > 0`, and `v` in `K_{ij}(v)` and `lambda_{ij}(v)` is the design
field with `delta = H`.

*Proof.* Fix `(i, j)` and `delta = H`. On the rectangle `T = tau L` lies in `[L/(4R), U L]`, so for
`N >= N_1(R, U)` we have `h q_max <= 1/2`, `T <= N^{1/3}`, and `1/T + T^2/N <= 4R/L + U^2 L^2/N
<= 5R/L`. By Lemma U5 only the faces `{i}`, `{j}` and `{i, j}` can carry a maximizer for
`N >= N_0`, and `{j}` never does, because `Phi_{tau,v}({j}) - Phi_{tau,v}({i}) = tau(q_j - q_i + H)
>= tau R >= 1/4` and the atoms are exact, so `M_{{j}} <= N^{-1/4} e^{O(1)} M_{{i}}` uniformly. It
remains to compare the pair with `{i}`. Proposition U4 and the exact singleton atom give,
uniformly on `P` and on the rectangle,

    D_N(T) := log M_{{i,j}}(p) - log M_{{i}}(p)
            = -L + delta' T + (1/2) log T + log( K_{ij}(v)/mu_i ) + E_5 ,   |E_5| <= C/L .

The function `Xi(T) = delta' T + (1/2) log T` is increasing with `Xi' >= delta' >= 2/U`. Let `T°`
solve `Xi(T°) = L - log(K_{ij}(v)/mu_i)`. Then `D_N(T) < 0` whenever `Xi(T) < Xi(T°) - C/L`, which
holds for `T <= T° - CU/(2L)`, and `D_N(T) > 0` for `T >= T° + CU/(2L)`. Where `D_N > 0` every
maximizer of the controlled atom lies on the pair (the comparison with the other faces being
settled), and where `D_N < 0` every maximizer is the singleton `{i}`. Hence
`tau^-_N >= T°/L - CU/(2L^2)` and `tau^+_N <= T°/L + CU/(2L^2)`, which is (a) with room to spare,
and `t_{ij,N} = T°/L + O(1/L^2)`.

To solve for `T°`, note that `T°/L` lies in `[t_ij/2, 2 t_ij]` for large `N` (as in the proof of
Theorem 4.7(i)), so `log T° = log L + log t_ij + O(log L/L)`, and

    delta' T° = L - (1/2) log L - (1/2) log t_ij - log( K_{ij}(v)/mu_i ) + O(log L/L) .

Dividing by `delta' L = L/t_ij` gives (b). The constant `c_ij` is bounded on `P` because `t_ij`
lies in `[1/R, U/2]`, `K_{ij}(v)` is continuous and positive on the compact set `P`, and
`mu_i >= mu_*`. The remainder is uniform because every constant above is.

For (c), at `tau_0` and a field `delta` on the retained pair `(i, 1)`, Lemma U5 leaves the two
singletons, whose atoms are exact. Their logarithms differ by
`log(mu_i/mu_1) + tau_0 L (q_1 - q_i + delta) + E_6` with `|E_6| <= 2 R^2 tau_0^2 L^2/N`, which
is increasing in `delta` with slope `tau_0 L`, so the switch is at
`delta = q_i - q_1 - log(mu_i/mu_1)/(tau_0 L) + O(L/N)`, and `|log(mu_i/mu_1)| <= log(1/mu_*)`.

For (d), the dimensionless coordinates `x_{i,N}/R` and `R t_{ij,N}` differ from their limits by
`O(log L/L)` uniformly, and by `O(1/L)` after the correction in (b), since `R t_ij |c_ij|/L
= O(1/L)`. For `N >= N_0` these errors are below the admissibility threshold of C-I3, whose
constant `C(d, b/R)` does not depend on the chain, and C-I3 gives the bounds. `qed`

Remark (what the start does). The only place where the start enters the first-order terms is the
singleton switch, through `log(mu_i/mu_1)/(tau_0 L)`. For the pair entry the start enters only
through `log(K_{ij}(v)/mu_i)` at order `1/L`. So the theorem holds with `mu_*` replaced by a
sequence `mu_{*,N}` as long as `log(1/mu_{*,N}) = o(L)`, with the rates in (b) to (d) replaced by
`O(log(1/mu_{*,N})/L)`. This is the exact dividing line between the class statement and the
counterexample of Section 6.

Remark (what is not claimed). Nothing above is uniform in the graph `G` or in `d`, and nothing is
claimed for `tau` outside the rectangle, where `T^2/N` need not be small. The uniqueness of the
zero of `D_N` is not needed and is not claimed. Faces with `T` between `N^{1/3}` and `N^{1/2}` do
not occur on the rectangle.

## 5. The delicate steps named in the brief

**Uniqueness and nondegeneracy of the saddle, and the off-saddle gap on the torus.** The saddle of
the torus integral is at `varphi = 0` for every `(p, alpha)`, by the nonnegativity of the
coefficients, and its Hessian `Theta' H Theta' = Theta' B^T Sigma_alpha B Theta'` is positive
definite with `det = prod theta_i^2 det Sigma_alpha/alpha_1^2`. All three factors are continuous
and positive on `P x K_0` by Lemma U1, so the least eigenvalue `sigma_min` of Lemma B.1 has a
positive minimum. The off-saddle gap of hypothesis (iii) is strict at every point, and Lemma B.1
turns it into a uniform `eta` by compactness of `(P x K_0) x {||varphi|| >= eps}`. The point is
that Lemma B.1 was written with an abstract compact parameter space, so nothing has to be
re-proved. The only new input is the joint continuity of the `varphi`-derivatives of `Psi` and
`chi` in `(p, alpha, varphi)`, which is the radius margin `delta_0` of Lemma U2.

**The finite cover of radii.** In the printed proof the cover is of `Delta_F \ U°` for one chain.
Covering `Y = {(p, beta)}` instead costs nothing, because the vectors `u_j` are fixed and
`theta_j(p) = A_F(p)u_j/u_j` is continuous. The constant `C_{theta_j(p)}` of Lemma 3.3 involves
`b(theta_j'(p))`, which is finite only where `varrho(A' - diag theta_j') < 0`. This is guaranteed
for every `theta` in `V_F(p)` by (A.3), with a strict inequality, so continuity in `p` holds. One
could instead cover with the Perron tilts `theta = q - v - lambda_F(v) 1` plus a fixed finite
family, but the covering above is simpler and matches the printed proof.

**The relative transfer `1 + O(T^2/N)`.** The constant comes from `Upsilon(1) <= C T`. The
printed proof takes the lower bound for `H(T alpha)` from Theorem 4.4, which is fine once Theorem
4.4 is uniform, but the single-word bound of Lemma U3 is simpler and manifestly uniform, with an
explicit constant `mu_* (b^2/R)^{M_0 - 1} eps_0^{M_0 - k}/prod (m^0_i - 1)!`. Both routes work. The
exponent `n_min >= eps_0 N` and `h q_max <= 1/2` are uniform.

**The rounding step.** The lattice point `n^0` with `|n^0_i - N alpha*_i| < 1` exists for
`N >= 1/(k eps_0)`, and the displacement bounds `C_F(n^0/N) >= K_F e^{-k B_1/N}` and
`T J(n^0/N) <= C_U k^2 T/N^2` use the uniform constants of the ball. In the crossing argument the
maximizers are compared through their values, never through derivatives of remainders, exactly as
in Theorem 4.7.

**The pair maximum against the singleton when `T` is as large as `U log N`.** On the rectangle
`T^2/N <= U^2 L^2/N`, which tends to zero, so the relative errors `O(1/T + T^2/N)` are `O(1/L)`
with a constant `5R` once `N >= N_1(R, U)`. The exact singleton atom has relative error
`R^2 T^2/N`. No step of the proof uses `T` beyond `N^{1/3}`.

**The common onset `N_0`.** The thresholds are the following. `N_1(R, U)` makes
`h q_max <= 1/2`, `T <= N^{1/3}` and `T^2/N <= 1` on the rectangle. `1/(k eps_0)` gives the lattice
point. `T_2` and `T_3` of Proposition U4 are below `L/(4R)` once `N` is large in terms of the
uniform constants. The `N_0` of Lemma U5 makes `N^{-3/4} (log N)^d e^{O(1)}` smaller than `1/2`.
The threshold of C-I3 bounds the admissible coordinate error. Each is a function of `(G, R, b, mu_*)` only. So one `N_0` works for the whole class, which
is the common onset.

## 6. The counterexample over all starts, and the thresholds

**The counterexample is a loss of compactness in the start.** In the two-state rate-one chain
with `tau = 1/4` and `v = (0, 1)`, the two singleton atoms are exact,
`M_{{1}} = mu_1 e^{-T}(1 + O(T^2/N))` and `M_{{2}} = mu_2 e^{-T(1 - 1)} = mu_2`. Their ratio is
`(mu_1/mu_2) N^{-1/4}(1 + o(1))`. For a fixed start this tends to zero and `{2}` wins, as the
leading score predicts. For `mu_2 = 1/(1 + 2N^{1/4})` the ratio is `2(1 + o(1))` and `{1}` wins
at every `N`. In the language of Theorem U6(c), the finite-horizon switch is displaced by
`log(mu_1/mu_2)/(tau L)`, and here `log(mu_1/mu_2) = (1/4)L + log 2`, so the displacement is
`1 + 4 log 2/L`, of order one. On the class `M(mu_*)` the same displacement is at most
`log(1/mu_*)/(tau_0 L)`, which tends to zero uniformly. So the failure over all starts is
precisely the failure of the bound `|log mu_i| <= log(1/mu_*)`, that is, of the compactness of the
set of starts, and it occurs at first order in the singleton comparison. No refinement of the
estimates can remove it, and the restriction to `min mu >= mu_*` (or to `log(1/min mu) = o(L)`,
as in the remark after Theorem U6) is the exact repair. The same mechanism does not affect the
pair entry at first order, because `mu` enters it through `log(K_{ij}(v)/mu_i)` at order `1/L`.

**`N^{1/3}` against `N^{1/2}`.** The face maximum formula is proved for `T <= N^{1/3}` and the
transfer for `T <= N^{1/2}`. On the rectangle `T <= U log N`, which is below `N^{1/3}` for
`N >= N_1(U)`, so the distinction does not matter for Theorem U6. It would matter only if the
design were run with `tau` growing with `N`, which it is not. The threshold `h q_max <= 1/2` is
`N >= 2 R U log N`, again a condition on `N` in terms of the class constants alone.

## 7. Numerical check on a two-state class

`02_T5_uniformity_check.py` computes the exact controlled atoms of two-state chains by the run
expansion, finds the smallest `tau` at which the pair beats both singletons (a sign change checked
to be unique on a grid, then bisection), and compares with the prediction of Theorem U6(b),
`t_N^pred = t (1 - log L/(2L)) + c/L`, where `K_{12}(v)` is computed from Proposition 4.2(b). The
class is `q_1 + q_2 <= R = 3`, `sqrt(q_1 q_2) >= b = 1` (for two states `||S||_2 = q_1 + q_2` and
`w = q_1 q_2`), the field is `v = (H, 0) = (6, 0)`, and the start is uniform. The quantity
`L^2 (t_N - t_N^pred)` should stay bounded as `N` grows, with a bound that does not blow up
across the six chains, which sit at the edges of the class. The output is in
`02_T5_uniformity_output.txt` and summarized in the table below.

| chain `(q_1, q_2)` | `t_12` | `c_12` | `K_12(v)` | `L^2 (t_N - t_N^pred)` at `N = 10^4, 10^5, 10^6, 10^7` |
|---|---:|---:|---:|---|
| (1.0, 1.0) | 6.162 | -16.55 | 2.953 | 12.86, 11.95, 11.87, 11.97 |
| (0.5, 2.0) | 7.631 | -23.68 | 4.033 | 18.79, 17.01, 16.66, 16.70 |
| (2.0, 0.5) | 4.712 | -10.89 | 2.324 | 7.90, 8.08, 8.25, 8.38 |
| (1.5, 1.5) | 2.824 | -5.85 | 2.364 | 4.50, 4.48, 4.56, 4.64 |
| (0.4, 2.5) | 8.222 | -26.87 | 4.581 | 21.36, 19.31, 18.87, 18.87 |
| (2.5, 0.4) | 4.141 | -8.98 | 2.151 | 6.25, 6.77, 7.01, 7.15 |

Reading the table. For every chain `L^2 (t_N - t_N^pred)` settles to a constant of the size of
`t_12^2`, with at most a slow drift of the order `log L` that the remainder `O(log L/L^2)` allows,
and the constants are largest for the chains with the largest `t_12`, that is, at the edge of
the class where `q_1` is smallest. Nothing blows up inside the class, which is what Theorem U6
asserts, and the six chains include both extreme points of the constraint `sqrt(q_1 q_2) = b`.
Two further remarks. First, the exact entry time is on the predicted side of the first-order
value `t_12 (1 - log L/(2L))` at every `N`, and the term `c_12/L` is numerically larger than the
`log log N` term (at `N = 10^7` and `(q_1, q_2) = (1, 1)` the first-order value is `5.63`, the
exact entry time `4.65`, and `c_12/L = -1.03`). So the correction `t_{ij,N}/(1 - log L/(2L))` of
Theorem U6(d) improves the rate but not the constant, and the paper should say that `c_ij`
depends on the unknown chain through `K_{ij}(v)` and cannot be removed without a second-order
estimate. Second, the coarse profile of the pair atom in `a` was unimodal in every evaluation
(the script asserts it), so the maximization is reliable at the stated precision. The run takes
about ninety seconds.

## 8. What the manuscript still has to do

- State Theorem U6 with the definition of `t_{ij,N}` and `x_{i,N}` through the sets of
  maximizer supports, as above, so that no uniqueness of a zero is needed.
- Print Lemma U1 (joint regularity) and the one-paragraph argument that Lemma B.1 applies with the
  parameter space `P x K_0`. Everything else is a reference to the printed proofs with the words
  "uniformly on `P`" added, and the table of Section 3 is the checklist.
- Replace the lower bound in Step 3 of the proof of Lemma 4.5 by the single-word bound, which is
  shorter and uniform without the local law.
- Cite the suppression lemma of C-I1 in its finite-`N` form (Lemma U5), which needs only Lemma 3.3
  with the Perron tilt and the exact singleton atom.
- Keep the class fixed in `G` and `d`. Uniformity in the graph is not claimed and is false in the
  obvious way (as `d` grows the number of faces and the constants of the Laplace lemma grow).

## Status

Proved under the stated hypotheses. Theorem U6 (class-uniform finite-horizon recovery with the
`log log N/(2 log N)` correction and the rate `O(1/log N)` after correction) holds on the compact
class `C(G; R, b) x M(mu_*)` with the protected design of C-I1. The proof is the compactness
argument of Section 4, which uses only the printed proofs of the paper, the two exact facts of
Section 2 and the explicit design constants. The external inputs that are cited and not re-proved
here are the suppression lemma of C-I1 (explicit Schur estimate, uniform by inspection of its
constants) and the stability bound of C-I3. The only hypothesis on the class that cannot be
dropped is `min mu >= mu_*` or its `o(log N)` weakening, and Section 6 shows why.
