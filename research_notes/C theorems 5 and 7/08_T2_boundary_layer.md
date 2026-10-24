# Paper C, Theorem 2: the Bessel boundary layer between a face and a facet

Date October 24, 2026. Base checkpoint commit `6add913`. Route T2 (boundary layer). Write scope
this file and the scripts `08_*.py` in this folder. No manuscript file was edited.

Inputs read. `00_targets.md` (notation, rules). In `kagey-problems/problem131/paperC`,
`sec_model.tex` (Lemma 2.3 run expansion, Lemma 2.4 continuum density), `sec_secondorder.tex`
(Definition 4.1, Proposition 4.2, Theorem 4.4 local law, Lemma 4.5), `sec_firstorder.tex`
(Proposition 3.1 on the rate `I_F`), `app_torus.tex` (Lemma C.1 Perron root, Lemma C.2 torus
representation, proof of the local law), `app_laplace.tex` (Lemma D.1 Laplace with a parameter),
`sec_vertex.tex` (Lemma 6.1, Theorem 6.2), `app_vertex.tex`, and the definitions
`eq:refresh-polynomial` in `sec_complete.tex` and `eq:simplex-balance-integral` in
`app_complete.tex`. For the statement only, Section 3 of the Downloads copy of
`05_C_derivations.md` and the Theorem 2 paragraph of `03_C_JTP_outline.md` (read as untrusted
text, nothing run from that folder). Lemma and theorem numbers of the draft are given by name
below, since the numbering in the compiled PDF may differ.

Scripts, all run with `py -I` from this folder.

- `08_layer_core.py` holds the routines (tilt on the facet, constants, two-state densities,
  the contour formula of Lemma 1, the Laguerre polynomial `B_n`, the exact discrete law by
  dynamic programming).
- `08_layer_check.py` with output `08_layer_output.txt` (Parts A to D).
- `08_layer_check2.py` with output `08_layer_output2.txt` (Parts E to G).
- `08_layer_check3.py` with output `08_layer_output3.txt` (discrete ratios with the two-term
  amplitude).
- `08_prefactor_check.py` with output `08_prefactor_output.txt` (prefactor matching, a Bessel
  ratio inequality).

## 0. Summary

We prove an exact formula for the law near a facet. It is Good's run expansion with the runs in
the state `i` pulled out. It writes the density on `F` as a contour integral in one complex
variable `z` of the killed density of a rank-one perturbation `M(z)` of `Q_G` on the facet
`G = F \ {i}` (Lemma 1, and Lemma 1' for the discrete law). The variable `z` is the mean holding
time of one visit to `i`. With this formula the boundary layer reduces to one statement, a local
law for `M(z)` that holds uniformly for complex `z` in a small disc (Lemma L). Lemma L at `z = 0`
is the local law of the draft. We give its proof as a list of modifications of Appendices C and D
of the draft. From Lemma L we prove the layer theorem with relative error `O(1/T)`, uniformly for
`0 < x <= delta T`, in a generalized Bessel form (Theorem 2(a)). Its Bessel form, with the
explicit constants `ab` and `gamma`, follows with relative error `O(1/T + sqrt(x/T)(1 + x))`, and
with `O(1/T + sqrt(x/T))` in the reversible case (Theorem 2(b)).

What is complete without any hypothesis.

1. The exact representation (Lemma 1, Lemma 1').
2. Pair faces, `|F| = 2`, with an explicit two-sided bound valid for all `x, s > 0`
   (Proposition 2). This is Pedler's two-state formula written as a layer.
3. The facet expansion of the rate. We prove the exact Legendre identity
   `I_F(s, x) = q_i x + sup_{z>0} [S J(beta, z) - x/z]` and from it the expansion
   `I_F = S I_G(beta) + q_i x - 2 sqrt(ab S x) + (gamma - q_i) x + O(x^{3/2} S^{-1/2})`, with
   `ab` and `gamma` given by the left and right tilt vectors at the facet profile, for every
   irreducible `Q` (Proposition 3). For reversible `Q` the expansion is exact with
   `gamma = q_i`. In general `gamma - q_i` is `ab/2` times an effective resistance between the
   law of the state from which the chain enters `i` and the law of the state into which it
   leaves `i`, so it vanishes exactly when the two laws agree.
4. Prefactor matching for reversible `Q`. The constant of the local law satisfies
   `C_F((1 - e) beta, e) ~ (4 pi)^{-1/2} (ab)^{1/4} e^{-3/4} C_G(beta)` as `e -> 0`, which is
   what the layer predicts (Proposition 4).

What is proved under a stated hypothesis. Theorem 2(a) and 2(b) for faces with `|F| >= 3`,
assuming Lemma L. The discrete form 2(c) needs in addition a discrete version of Lemma L. The
numerics (Parts B to G) agree with every prediction, including the non-reversible `gamma`.

Two corrections to the plan's heuristic. The constant `c` in front of the kernel is `1`, and the
first correction is `c_1 z_* I_0(Z)/I_1(Z)` with an explicit `c_1`. The constant `gamma` is not
`q_i` for non-reversible `Q`, and for non-reversible `Q` the pure Bessel form with a constant
`gamma` is accurate only for `x << T^{1/3}`. Beyond that the generalized kernel of Theorem 2(a)
is needed, and it is accurate up to `x = delta T`. The lattice sublayer `n_i = O(1)` of the
heuristic is not a separate regime when `T^2/N -> 0`. Lemma 6.1 of the draft shows that the
lattice kernel and the Bessel kernel differ by a factor in `[1 - w/2, 1]` with `w ~ ab T^2/N`,
uniformly in `n_i`. The lattice regime appears only at `T` of order `sqrt N`, which is the regime
of the near-vertex theorem.

## 1. Setting and the statement we aim at

Let `F` be an irreducible face, `i` in `F`, and `G = F \ {i}` with `g = |G| = |F| - 1 >= 1`. We
assume that `G` satisfies (H), so `G` is irreducible and `mu(G) > 0`. The start mass `mu_i` may be
zero. Since `F` is irreducible, the vectors

    c^-_j = q_ji  (rate from j into i),      c^+_j = q_ij  (rate from i into j),      j in G,

are nonzero and nonnegative. For `z` in `C` put

    M(z) = Q_G + z c^- (c^+)^T,      pi(z) = mu_G + z mu_i c^+,      e(z) = 1 + z c^-.

Occupation coordinates. On `E_F` (the chain stays in `F` up to time `T` and visits all of `F`)
let `s` in `(0, inf)^G` be the time spent in `G`, `S = sum_j s_j`, and `x = T - S` the time
spent in `i`. We write `f_F(s, x)` for the density of the occupation times on `E_F` in the
coordinates `(s_2, ..., s_g, x)`, and `f_G(s)` for the density of the occupation times on `E_G`
at total time `S` in the coordinates `(s_2, ..., s_g)` (for `g = 1`, `f_G(S) = mu_j e^{-q_j S}`).
These are `e^{-<q,t>} H(t)` of Lemma 2.4 of the draft. The profile is `beta = s/S` in
`Delta_G^o`. In visit fractions `alpha_i = x/T`, and `x = T n_i/N` for the discrete chain.

Facet constants. Let `r_beta`, `l_beta` be the optimal vectors of `I_G(beta)` (Definition 4.1 of
the draft for the face `G`), normalized by `l_beta . r_beta = 1`, so `l_beta = beta / r_beta`.
Put

    a = c^- . l_beta,      b = c^+ . r_beta,      ab = a b,
    pi^in_j  = c^-_j l_{beta,j} / a,      pi^out_j = c^+_j r_{beta,j} / b,
    kappa_jk = l_{beta,j} q_jk r_{beta,k} + l_{beta,k} q_kj r_{beta,j}   (j != k in G),

let `L_beta` be the Laplacian of the conductances `kappa` on `G`, with pseudo-inverse `L_beta^+`,
and

    gamma(beta) = q_i + (ab/2) (pi^out - pi^in)^T L_beta^+ (pi^out - pi^in).

Only `ab` is intrinsic, since `a` and `b` change in opposite ways when `r_beta` is scaled. The law
`pi^in` is the law of the state from which the tilted chain enters `i`, and `pi^out` is the law of
the state into which it returns. The conductances `kappa` are those of the additive
reversibilization of the tilted generator of the draft, `kappa_jk = beta_j (Qhat_beta)_jk +
beta_k (Qhat_beta)_kj`.

Let `J(beta, z)` be the rate `I_{M(z)}(beta)` of the Metzler matrix `M(z)` (Section 4 below
shows that it is real-analytic near `z = 0`), and `C(beta, z)` the local-law constant of the
weighted chain `(M(z), pi(z), e(z))` at `beta`, that is Definition 4.1 of the draft with start
`pi(z)` and end vector `e(z)` in place of `mu` and `1`. Put `c_1(beta) = d/dz log C(beta, z)` at
`z = 0`. Finally

    Z = 2 sqrt(ab S x),      z_* = sqrt(x / (ab S)),
    Bessel kernel    B_beta(x, S) = e^{-gamma x} sqrt(ab S / x) I_1(Z),
    generalized kernel
        K_beta(x, S) = e^{-q_i x} (1/(2 pi i)) oint_{|z| = z_*} e^{x/z} (C(beta,z)/C(beta,0))
                        e^{S (I_G(beta) - J(beta,z))} z^{-2} dz .

**Theorem 2 (the boundary layer, target statement).** Let `F`, `i`, `G` be as above and let
`Kc` be a compact subset of `Delta_G^o`. There are `delta > 0`, `T_0` and `C` such that the
following hold uniformly for `beta` in `Kc`, `T >= T_0` and `0 < x <= delta T`, with
`S = T - x` and `s = S beta`.

(a) `f_F(s, x) = f_G(s) K_beta(x, S) (1 + E)` with `|E| <= C/T`.

(b) `f_F(s, x) = f_G(s) B_beta(x, S) (1 + E)` with `|E| <= C (1/T + sqrt(x/T) (1 + x))`. If `Q`
is reversible on `F`, then `gamma = q_i`, `|E| <= C (1/T + sqrt(x/T))`, and with the two-term
kernel `B_beta (1 + c_1 z_* I_0(Z)/I_1(Z))` the error is `C (1 + x)/T`.

(c) (Discrete form.) Uniformly also for `T <= N^{1/3}`, `supp n = F`, `nhat/(N - n_i)` in `Kc`
and `1 <= n_i <= delta N`, with `h = T/N`, `N' = N - n_i`, `x = h n_i`, `S = h N'`,

    P_N(n) = P_{N'}(nhat) e^{-(gamma - q_i) x} (1 - h q_i)^{n_i} B_{n_i}( ab S h / (1 - h q_i) )
             (1 + O(1/T + sqrt(x/T)(1 + x) + T^2/N)),

where `P_{N'}(nhat)` is the probability of the composition `nhat` (with `n_i = 0`) for the same
chain run for `N'` steps and `B_n(w) = sum_{m=1}^n binom(n-1, m-1) w^m / m!` is the polynomial
of `eq:refresh-polynomial`. By Lemma 6.1 of the draft the Laguerre factor equals
`h e^{-q_i x} sqrt(ab S/x) I_1(Z)` times a factor in `[1 - w/2, 1]` with `w = ab S h/(1 - hq_i)`,
up to a factor `1 + O(h)`, uniformly in `n_i`. So it may
be replaced by `h B_beta(x, S) e^{(gamma - q_i)x}` at the cost of `O(T^2/N)`.

The three regimes. For `Z <= 1`, that is `x <= 1/(4 ab S)` or `n_i <~ N/(ab T^2)`, the kernel is
`ab S (1 + O(Z^2))` and one visit to `i` dominates. Then `P_N(n) ~ P_{N'}(nhat) h^2 ab N'`, one
excursion `j -> i -> j'` with `N'` possible places. For `Z >> 1` there are about `Z/2 =
sqrt(ab S x)` visits of mean length `z_*`, and `I_1(Z) ~ e^Z/sqrt(2 pi Z)` reproduces the
`sqrt(alpha_i)` singularity of `I_F` (Proposition 3). The lattice is felt only when the mean
visit length `z_*` is of order `h`, that is `n_i <~ ab T^2/N`. For `T^2 = o(N)` this range holds
no positive integer, and the discrete correction is uniformly `O(T^2/N)`.

## 2. The exact representation

**Lemma 1 (Good's expansion with the runs in `i` pulled out, continuum).** Let `F` be any face,
`i` in `F`, `G = F \ {i}`. For `z` in `C` let `A(z)` be the off-diagonal part of `M(z)` and
`d(z) = q_G - z c^- o c^+` (entrywise product), so that `M(z) = A(z) - diag d(z)`.
For `s` in `(0, inf)^G` define

    Phi(z)(s) = e^{-<d(z), s>} sum_{m in Z_{>=1}^G} W_z(m) prod_{j in G} s_j^{m_j - 1}/(m_j - 1)!,
    W_z(m) = sum_w pi(z)_{w_1} prod_{l < |w|} A(z)_{w_l w_{l+1}} e(z)_{w_{|w|}},

the sum over the words `w` in `G` with no two equal neighbours and `m_j` letters `j`. Then
`z -> Phi(z)(s)` is entire, `Phi(0)(s) = f_G(s)`, and for `x > 0`

    f_F(s, x) = e^{-q_i x} sum_{K >= 1} x^{K-1}/(K-1)!  [z^K] Phi(z)(s)                     (2.1)
              = e^{-q_i x} (1/(2 pi i)) oint_{|z| = rho} e^{x/z} Phi(z)(s) z^{-2} dz       (2.2)

for every `rho > 0`.

*Proof.* By Lemma 2.4 of the draft, `f_F(s, x) = e^{-<q_G, s> - q_i x} H_F(s, x)` with `H_F` the
sum over words `c` in `F` with no equal neighbours. Fix such a word with `K = m_i(c) >= 1`
letters `i`. The letters `i` are isolated in `c`. Delete them. We get a word `c'` in `G`, in which
equal neighbours occur exactly where `c` had `j i j`. We mark the places of `c'` where a letter
`i` was deleted. A mark between two letters `j, j'` of `c'` carries the weight
`q_ji q_ij' = c^-_j c^+_{j'}`, a mark before the first letter `j'` carries `mu_i c^+_{j'}` (the
word started in `i`), and a mark after the last letter `j` carries `c^-_j` (the word ended in
`i`). Two neighbours of `c'` without a mark are different and carry `q_jj'`. So the weight
`mu_{c_1} prod q_{c_l c_{l+1}}` of `c` is the product of these weights. The factor
`t_i^{m_i - 1}/(m_i - 1)!` is `x^{K-1}/(K-1)!`. Between two different letters there is at most
one mark, and between two equal letters exactly one. Group the marked words `c'` by the reduced
word `w` (merge each block of equal letters of `c'` into one letter) and by the number `n_l` of
marks inside the `l`-th block. A letter `j` with `rho_j` blocks has `m_j = rho_j + sum n_l`
letters in `c'`. Summing over the `n_l` with weight `(c^-_j c^+_j)^{n_l}` uses the identity

    sum_{n >= 0} binom(n + rho - 1, rho - 1) y^n s^{rho + n - 1}/(rho + n - 1)!
        = e^{ys} s^{rho - 1}/(rho - 1)!,

which holds since `binom(n + rho - 1, rho - 1)/(rho + n - 1)! = 1/(n! (rho - 1)!)`. So the blocks
give the factor `e^{z c^-_j c^+_j s_j}`, which is the diagonal part of `d(z)`, when every mark is
counted by `z`. The marks between different letters give `A(z)`, the first and last marks give
`pi(z)` and `e(z)`. Collecting the powers of `z` gives (2.1). The entries of `A(z)`, `pi(z)`,
`e(z)` are polynomials in `z`, and the bound `W(m) <= k^M q_max^{M-1}` of the draft holds with
`q_max` replaced by `q_max (1 + |z| q_max)`, so the series converges for every `z` and
`Phi(.)(s)` is entire. Then
`oint e^{x/z} z^{-2} Phi(z) dz/(2 pi i) = sum_{n >= 0} x^n/n! [z^{n+1}] Phi(z)`, by expanding
`e^{x/z}` and integrating term by term on the circle, which is (2.2). For `z = 0` the words `c'`
carry no mark and `Phi(0)(s)` is the sum of Lemma 2.4 for the face `G`. ∎

In words, `Phi(z)` is the killed density on the facet for the chain in which each visit to `i`
is replaced by an instantaneous jump `j -> j'` of rate `z c^-_j c^+_{j'}`. The holding times of
the `K` visits have total `x` with density `q_i^K x^{K-1} e^{-q_i x}/(K-1)!`, and each return
carries `c^+_{j'}/q_i`, so the powers of `q_i` cancel and leave `x^{K-1}/(K-1)!`. This is the
series of the plan's heuristic, with `(Ta)^K/K!` replaced by the exact coefficient
`[z^K] Phi(z)(s)`. Part B of `08_layer_check.py` checks (2.2) against the exact discrete law for
two three-state chains. The ratio of `P_N(n)/h^2` to (2.2) is `0.99419, 0.99740, 0.99877` at
`N = 200, 400, 800` for the path and `0.8876, 0.9447, 0.9726` for the non-reversible cycle
(`T = 6`), so the deviation halves with `N`, as the `O(T^2/N)` of Lemma 4.5 predicts.

**Lemma 1' (discrete form).** Let `supp n = F`, `n_i >= 1`, `N' = N - n_i`, `hq_max <= 1`. Then

    P_N(n) = sum_{K >= 1} binom(n_i - 1, K - 1) (1 - h q_i)^{n_i - K} [z^K] P^{(z)}_{N'}(nhat),
    P^{(z)}_{N'}(nhat) = sum_x pi^h(z)_{x_1} prod_{t < N'} (I + h Q_G + z h^2 c^- (c^+)^T)_{x_t x_{t+1}} e^h(z)_{x_{N'}},

the sum over the words `x_1 ... x_{N'}` in `G` with composition `nhat`, where
`pi^h(z) = mu_G + z h mu_i c^+` and `e^h(z) = 1 + z h c^-`. For `z = 0`,
`P^{(0)}_{N'}(nhat) = P_{N'}(nhat)`.

*Proof.* Delete the maximal blocks of `i` from a path with composition `n`. What is left is a
path `x_1 ... x_{N'}` in `G`. A block of length `len` between `x_t = j` and `x_{t+1} = j'`
replaces the factor `(I + hQ)_{jj'}` by `h q_ji (1 - h q_i)^{len - 1} h q_ij'`. A block at the
start replaces `mu_{x_1}` by `mu_i (1 - hq_i)^{len - 1} h q_{i x_1}`, and a block at the end adds
`h q_{x_{N'} i} (1 - h q_i)^{len - 1}`. Count the blocks by `z`. The block lengths form a
composition of `n_i` into `K` positive parts, and there are `binom(n_i - 1, K - 1)` of them. ∎

## 3. Pair faces

**Proposition 2 (pair faces, all x).** Let `F = {j, i}` with `q_ji, q_ij > 0` and `mu_j > 0`,
`G = {j}`, `w = q_ji q_ij`. Then for all `s, x > 0`, with `Z = 2 sqrt(w s x)`,

    f_F(s, x) = mu_j e^{-q_j s - q_i x} [ sqrt(w s/x) I_1(Z) + (q_ji + (mu_i/mu_j) q_ij) I_0(Z)
                                         + (mu_i/mu_j) sqrt(w x/s) I_1(Z) ].

Here `ab = w`, `gamma = q_i`, `f_G(s) = mu_j e^{-q_j s}`, and

    0 <= f_F(s, x) / [ f_G(s) e^{-q_i x} sqrt(w s/x) I_1(Z) ] - 1
      <= (q_ji + (mu_i/mu_j) q_ij) ( 1/(w s) + sqrt(x/(w s)) ) + (mu_i/mu_j) x/s .

*Proof.* For `g = 1` the only words in `G` are `j`, so
`Phi(z)(s) = (mu_j + z mu_i q_ij)(1 + z q_ji) e^{-(q_j - z w) s}`. With `z = z_* t`,
`z_* = sqrt(x/(ws))`, we have `x/z + w s z = (Z/2)(t + 1/t)`, and the generating function
`e^{(Z/2)(t + 1/t)} = sum_k I_k(Z) t^k` gives
`oint e^{x/z + wsz} z^{n-2} dz/(2 pi i) = z_*^{n-1} I_{n-1}(Z)`. Put this into (2.2) for
`n = 0, 1, 2`. The bound uses `I_0(Z)/I_1(Z) <= (1 + sqrt(1 + Z^2))/Z <= 1 + 2/Z`, the lower
bound for `I_1/I_0` of Amos (Math. Comp. 28, 1974). `08_prefactor_check.py` confirms it on a
grid of `Z` in `[1e-6, 1e3]` (maximum of the ratio `0.9999995`). Finally
`sqrt(x/(ws)) (1 + 2/Z) = sqrt(x/(ws)) + 1/(ws)`. ∎

This is the occupation-time density of the two-state chain of Pedler (J. Appl. Probab. 8, 1971),
written as a boundary layer. Kovchegov, Meredith and Nir (Statist. Probab. Lett. 80, 2010) give
the same Bessel densities. The bound is uniform in `x`. It is `O(1/T + sqrt(x/T))` for
`x <= T/2`. For pair faces Theorem 2(a) and 2(b) hold with no restriction on `x`, and the error
term `sqrt(x/T)` is attained, since the middle term is exactly of that size. The case `g = 1`
of Lemma L holds with no error term, which is why this case closes.

## 4. The constants for every irreducible Q

The rate on `F`, written as a function of occupation times, is homogeneous of degree one,
`I_F(s, x) = T I_F((s, x)/T)`, and the same holds on `G`. Put
`Psi_beta(u) = sum_j beta_j (q_j - sum_{k in G} q_jk u_k/u_j)` and
`P_beta(u) = (c^+ . u)(sum_j c^-_j beta_j / u_j)` for `u` in `(0, inf)^G`. Then
`J(beta, z) = sup_u [Psi_beta(u) - z P_beta(u)]` for real `z >= 0`, since
`sum_j beta_j (-(M(z) u)_j/u_j) = Psi_beta(u) - z P_beta(u)`.

**Proposition 3 (the facet expansion of the rate).** Let `F` be irreducible, `i` in `F`, and
`G = F \ {i}` irreducible.

(i) For `s = S beta` with `beta` in `Delta_G^o` and `x > 0`,

    I_F(s, x) = q_i x + sup_{z > 0} [ S J(beta, z) - x/z ].

(ii) `J(beta, .)` is real-analytic near `0`, with `J(beta, 0) = I_G(beta)`,
`d_z J(beta, 0) = -ab` and `d_z^2 J(beta, 0) = 2 j_2` where
`j_2 = (1/2) grad P^T L_beta^+ grad P`, `grad P = ab (pi^out - pi^in)`. So
`j_2/ab = gamma - q_i >= 0`.

(iii) Uniformly for `beta` in a compact subset of `Delta_G^o` and `x/S <= delta`,

    I_F(s, x) = S I_G(beta) + q_i x - 2 sqrt(ab S x) + (gamma - q_i) x + O(x^{3/2} S^{-1/2}).

In visit fractions, `I_F((1 - a_i) beta, a_i) = (1 - a_i) I_G(beta) + q_i a_i
- 2 sqrt(ab (1 - a_i) a_i) + (gamma - q_i) a_i + O(a_i^{3/2})`.

(iv) If `nu_j q_jk = nu_k q_kj` on `F` for some positive `nu`, then `pi^in = pi^out`, `gamma = q_i`,
`J(beta, z) = I_G(beta) - z ab` for all `z >= 0`, `ab = (sum_{j in G} sqrt(w_ij beta_j))^2`, and
`I_F(s, x) = S I_G(beta) + q_i x - 2 sqrt(ab S x)` exactly.

*Proof.* (i) In the supremum that defines `I_F(s, x)` put `u = (u_G, epsilon)` with
`epsilon = u_i`. The terms with `epsilon` are `-epsilon sum_j s_j c^-_j/u_j - (x/epsilon)(c^+ . u_G)`.
Both coefficients are positive since `c^-, c^+` are nonzero. The supremum over `epsilon > 0` is
`-2 sqrt(x S P_beta(u_G))`. So `I_F(s, x) = q_i x + sup_u [S Psi_beta(u) - 2 sqrt(x S P_beta(u))]`.
Now `2 sqrt(x S P) = inf_{z > 0} [S z P + x/z]`, and exchanging the two suprema gives (i).

(ii) Write `u = e^psi`. The function `psi -> Psi_beta(psi) - z P_beta(psi)` is concave for real
`z >= 0`. At `z = 0` its maximizer `psi_0 = log r_beta` is unique up to a constant and its
Hessian `-L_beta` is negative definite on the complement of the constants. Indeed
`Psi_beta = const - sum_{j != k} beta_j q_jk e^{psi_k - psi_j}`, and the Hessian of
`sum w_jk e^{psi_k - psi_j}` is the Laplacian with conductance `w_jk + w_kj` on `{j, k}`, which
at `psi_0` is `kappa_jk` (use `beta_j / r_{beta,j} = l_{beta,j}`). The kernel of `L_beta` is the
constants since `G` is irreducible. Both functions are invariant under adding a constant to
`psi`. By the implicit function theorem on the complement of the constants, the critical point
`psi(z)` is real-analytic near `0`, and for real `z >= 0` it is the maximizer by concavity. So
`J(beta, z) = Psi_beta(psi(z)) - z P_beta(psi(z))` is real-analytic. The envelope theorem gives
`d_z J = -P_beta(psi(z))`, so `d_z J(beta, 0) = -P_beta(r_beta) = -(c^+ . r_beta)(c^- . l_beta)
= -ab`. Differentiating once more, `d_z^2 J(beta, 0) = -grad P . psi'(0)` with
`-L_beta psi'(0) = grad P`, which gives `grad P^T L_beta^+ grad P`. Finally
`d_{psi_m} P = r_{beta,m} c^+_m (c^- . l_beta) - (c^+ . r_beta) c^-_m l_{beta,m} =
ab (pi^out_m - pi^in_m)`.

(iii) By (i) and the expansion
`P_beta(e^psi) = ab + grad P . (psi - psi_0) + O(|psi - psi_0|^2)`, we write
`I_F(s, x) - q_i x = sup_psi [S Psi_beta(psi) - 2 sqrt(x S P_beta(psi))]`. Comparing the value at
`psi_0` with the value at a maximizer `psi*` gives
`Psi_beta(psi_0) - Psi_beta(psi*) <= 2 sqrt(x/S) sup P^{1/2}` on the bounded set where the
maximizer lies (the bounded set of the proof of Proposition 3.1(b) of the draft, which is
uniform for `beta` in a compact set). By the strict concavity near `psi_0`, `psi* - psi_0 =
O((x/S)^{1/4})` at first, and then the Taylor expansion of `S Psi_beta - 2 sqrt(xS) P^{1/2}` to
second order around `psi_0` gives `psi* - psi_0 = -2 sqrt(x/S) L_beta^+ grad(P^{1/2}) + O(x/S)`
and the value `S I_G(beta) - 2 sqrt(ab x S) + 2 x grad(P^{1/2})^T L_beta^+ grad(P^{1/2}) +
O(S (x/S)^{3/2})`. Since `grad(P^{1/2}) = grad P/(2 sqrt(ab))`, the middle coefficient is
`j_2/ab`. The fraction form follows from homogeneity with `S = (1 - a_i) T`, `x = a_i T`.

(iv) With `l_{beta,j} = sqrt(beta_j nu_j)` and `r_{beta,j} = sqrt(beta_j/nu_j)` (Proposition 4.2(b)
of the draft) we get `c^-_j l_{beta,j} = q_ji sqrt(beta_j nu_j) = nu_i q_ij sqrt(beta_j/nu_j)`, so
`pi^in` is proportional to `pi^out` and they are equal. More is true. The matrix `M(z)` is
reversible with respect to `nu_G` for every `z >= 0`, since
`nu_j c^-_j c^+_k = nu_i q_ij q_ik` is symmetric in `j, k`. So `grad P(psi_0) = 0` and `psi_0` is a
critical point of the concave function `Psi_beta - z P_beta` for every `z`, which gives
`J(beta, z) = I_G(beta) - z P_beta(r_beta)`. Then (i) gives
`sup_z [-S z ab - x/z] = -2 sqrt(ab S x)`. The value of `ab` is
`(sum_j q_ji sqrt(beta_j nu_j))(sum_j q_ij sqrt(beta_j/nu_j)) = (sum_j sqrt(w_ij beta_j))^2` by the
same symmetry. This agrees with Proposition 3.1(c) of the draft, which gives the same exact
formula directly from the pair sum. ∎

Part A of `08_layer_check.py` checks (ii) and (iv). For the path `1-2-3`, `beta = (1/2, 1/2)`,
`ab = 1/2` and `gamma = q_3 = 1`. For the reversible chain with `nu = (1, 2, 4)` and symmetric
weights `s_12 = 1`, `s_13 = 1/2`, `s_23 = 2` (`q_jk = s_jk sqrt(nu_k/nu_j)`), at `beta = (1/2, 1/2)`,
`ab = 3.125` both from the tilt and from `(sum sqrt(w_3j beta_j))^2`, and `pi^in = pi^out =
(0.2, 0.8)`. For the non-reversible cycle `q_12 = q_23 = q_31 = 2`, `q_21 = q_32 = q_13 = 1`, at
`beta = (1/2, 1/2)`, `ab = 5.181981` (finite differences of `J` give `5.181971`), `j_2 = 2.165515`
(finite differences `2.151`, with an `O(z)` truncation error), `pi^in = (0.261, 0.739)`,
`pi^out = (0.739, 0.261)`, and `gamma = 3.417893` against `q_3 = 3`. The reversible formula
`(sum sqrt(w beta))^2 = 4` is wrong for this chain, as it should be.

The proposition gives the exponent half of the matching between the layer and the local law.
For `1/T << x << T` the Bessel kernel is
`(4 pi)^{-1/2} (ab S)^{1/4} x^{-3/4} exp(2 sqrt(ab S x) - gamma x)(1 + O(1/Z))`, and (iii) says that
`f_G(s) B_beta(x, S)` and `T^{-g/2} C_F(alpha) e^{-T I_F(alpha)}` (the local law of the draft in
occupation coordinates) have the same exponent up to `O(x^{3/2} S^{-1/2})`. For the powers and
constants to match as well we need
`C_F((1 - e) beta, e) ~ (4 pi)^{-1/2} (ab)^{1/4} e^{-3/4} C_G(beta)` as `e -> 0`.

## 5. Prefactor matching and the first amplitude correction

**Proposition 4 (prefactor matching, reversible).** Let `Q` be reversible on `F` with respect to
`nu`, `G` irreducible with `mu(G) > 0`, `g >= 1`. Uniformly for `beta` in a compact subset of
`Delta_G^o`, as `e -> 0`,

    C_F((1 - e) beta, e) = (4 pi)^{-1/2} (ab(beta))^{1/4} e^{-3/4} C_G(beta) (1 + O(sqrt e)),

with `C_G(beta) = mu_j` when `G = {j}`.

*Proof.* Use Proposition 4.2(b) of the draft at `alpha = ((1 - e) beta, e)`. The vectors are
`r_alpha = sqrt(alpha/nu)` and `l_alpha = sqrt(alpha nu)`. On `G` they are `sqrt(1 - e)` times
`r_beta`, `l_beta`, and at `i` they are `O(sqrt e)`. So
`(mu . r_alpha)(l_alpha . 1) = (mu_G . r_beta)(l_beta . 1)(1 + O(sqrt e))`. Next
`prod alpha = e (1 - e)^g prod beta`. The conductances are `c_jk(alpha) = (1 - e) c_jk(beta)` on
`G` and `c_ij(alpha) = sqrt(e (1 - e) beta_j) q_ij sqrt(nu_i/nu_j) = sqrt(e(1 - e))
sqrt(w_ij beta_j)` at `i`. A spanning tree of `F` with `m` edges at `i` has weight
`O(e^{m/2})`. The trees with one edge at `i` are a spanning tree of `G` plus an edge `{i, j}`. So
`tree(c(alpha)) = sqrt e sqrt(ab) tree(c_G(beta)) (1 + O(sqrt e))`, using
`sum_j sqrt(w_ij beta_j) = sqrt(ab)` from Proposition 3(iv). Put these into the formula of
Proposition 4.2(b), with `k = g + 1`. ∎

`08_prefactor_check.py` evaluates both sides for the reversible chain above. At
`beta = (1/2, 1/2)` the target is `0.375066`, and `e^{3/4} C_F/C_G` is `0.4501, 0.3977, 0.3821,
0.3773, 0.3758` at `e = 1e-2, ..., 1e-6`. The deviation falls by `sqrt 10` per decade, as the
`O(sqrt e)` predicts. At `beta = (0.3, 0.7)` the target is `0.393639` and the last value is
`0.394368`.

The amplitude correction. The first correction to the Bessel form comes from the `z`-dependence
of `C(beta, z)`. It contributes `c_1 oint e^{x/z + abSz} z^{-1} dz/(2 pi i) = c_1 I_0(Z)` to the
contour integral, which is `c_1 z_* I_0(Z)/I_1(Z)` relative to the main term. That is
`c_1/(ab S)` for small `Z` and `c_1 z_*` for large `Z`. For reversible `Q`, `r_beta` does not move
with `z` (Proposition 3(iv)), and from Proposition 4.2(b) of the draft applied to `M(z)`,

    c_1 = mu_i b/(mu_G . r_beta) + a/(l_beta . 1) + (ab/2) sum_{j<k in G} R_jk pi_j pi_k,

where `pi = pi^in = pi^out` and `R_jk` is the effective resistance between `j` and `k` in the
network with conductances `l_{beta,j} q_jk r_{beta,k}`. The first term comes from the start in
`i`, the second from the end in `i`, and the third from `d log tree/d c_e = R_e` (Kirchhoff) with
`d c_jk/dz = l_{beta,j} c^-_j c^+_k r_{beta,k} = ab pi_j pi_k`. Part E of `08_layer_check2.py`
compares this with finite differences of the closed two-state amplitude. For the path at
`beta = (1/2, 1/2)` both give `c_1 = 1`, and at `beta = (0.3, 0.7)` both give `1.208712`. For the
reversible chain they give `3.303301` and `3.604385`. For the non-reversible cycle the finite
difference gives `3.996320`.

## 6. General faces

### 6.1 The one input, a local law with a complex parameter

**Lemma L (local law for the perturbed facet chain).** Let `G` satisfy (H) with `g >= 2` and let
`Kc` be a compact subset of `Delta_G^o`. There are `z_0 > 0` and `C` such that, uniformly for
`beta` in `Kc`, `S >= 1` and complex `|z| <= z_0`,

    Phi(z)(S beta) = S^{-(g-1)/2} C(beta, z) e^{-S J(beta, z)} (1 + eps),      |eps| <= C/S,

where `J(beta, .)` and `C(beta, .)` are holomorphic on `|z| < 2 z_0`, jointly continuous in
`(beta, z)`, real on real `z`, equal to `I_{M(z)}(beta)` and to the local-law constant of
`(M(z), pi(z), e(z))` for real `0 <= z < 2 z_0`, and `C(beta, 0) = C_G(beta) > 0`.

At `z = 0` this is the local law of the draft for the face `G` (Theorem 4.4), in occupation
coordinates. For `g = 1` the analogous statement holds with `eps = 0` (Section 3).

*Proof outline.* Every step is a change of Appendices C and D of the draft.

Step 1 (torus representation with complex weights). Lemma C.2 of the draft applies to any word
sum whose weights are dominated in modulus by a nonnegative system for which the geometric
series converge. Here `|A(z)| <= A_G + |z| offdiag(c^- (c^+)^T)` entrywise, and the same for
`pi(z)` and `e(z)`. The end vector `e(z)` changes the factor `b(z')` of Lemma C.2 into
`(pi_1 + pi'^T X b_1)(e_1 + a_1^T X e')`, with the same proof. So `Phi(z)(t) =
e^{-<d(z), t>} (2 pi)^{-(g-1)} int e^{t_1 g_z(z') + sum_{j >= 2} t_j z_j} b_z(z') prod z_j dphi`
on every torus whose radii `rho'` satisfy `varrho(|A(z)|' - diag rho') < 0`.

Step 2 (radii for complex `z`). For real `z` the draft uses the radii `theta'(beta, z)`, the
tilt of `M(z)` at `beta`. The point `theta'(beta, 0)` is a nondegenerate critical point of
`z' -> beta_1 g_0(z') + sum_{j >= 2} beta_j z_j`, with Hessian `B^T Sigma_beta B` (proof of the
local law in Appendix C of the draft). By the holomorphic implicit function theorem there is a
critical point `z'_c(beta, z)` in `C^{g-1}`, holomorphic in `z` and real-analytic in `beta`, for
`|z| <= z_0`. Write `z'_c = rho o e^{i phi_c}` with `rho > 0` and real `phi_c`. Take the torus of
radii `rho` and rotate it by `phi_c`, which does not change the integral. Then the critical point
lies on the torus at `phi = 0`, because `d/d phi_j = i z_j d/d z_j`. For `|z| <= z_0` small, `rho`
is close to `theta'(beta, 0)` and the convergence condition of Step 1 holds, since it holds
strictly at `z = 0` by (C.4) of the draft.

Step 3 (Laplace with a complex Hessian). The phase `Psi(beta, z, phi)` now has a complex value at
`phi = 0`, zero gradient there, and Hessian `-Jc(beta, z)` complex symmetric with
`Jc(beta, 0)` real positive definite. So `Re Jc >= (sigma_min/2) I` for `|z| <= z_0`. The gap
`Re Psi(phi) - Re Psi(0) <= -eta` on `||phi|| >= epsilon` holds at `z = 0` (proof of the local
law), so it holds with `eta/2` for `|z| <= z_0` by uniform continuity on the compact set
`Kc x {|z| <= z_0} x {||phi|| >= epsilon}`. Lemma D.1 of the draft holds for such phases. Its
proof uses `x^T Jc x >= sigma_min |x|^2` only through the modulus of the Gaussian weight, which
becomes `Re(x^T Jc x)`, and the Gaussian integral is `(2 pi)^{m/2} det(Jc)^{-1/2}` with the
branch continued from real `Jc`. The odd terms still integrate to zero.

Step 4 (identification). The critical value gives `-S J(beta, z)` and the amplitude gives
`C(beta, z)`. Both are holomorphic in `z`. For real `z` they equal the rate and the constant of
the draft for `M(z)`, by the same computation as in the proof of the local law. The parameter set
`Kc x {|z| <= z_0}` is compact, and the joint continuity of the `phi`-derivatives follows from
analyticity, as in the paragraph "Regularity" of that proof. ∎

What is not yet written out in full. Steps 1 and 4 are routine. In Step 2 the continuity of
`rho(beta, z)` and `phi_c(beta, z)` follows from the implicit function theorem. In Step 3 the
change to Lemma D.1 is two lines. We have checked each step, but the complete written proof with
explicit constants is not yet in this note. We list Lemma L as the stated hypothesis of
Theorem 2 for `|F| >= 3` until it is written out.

### 6.2 Proof of Theorem 2(a) from Lemma L

Fix `beta` in `Kc` and `0 < x <= delta T`, so `S = T - x >= T/2`. Write
`Lam(z) = S^{-(g-1)/2} C(beta, z) e^{-S J(beta, z)}` for the leading form. By Lemma L,
`f_G(s) = Lam(0)(1 + O(1/S))`. By (2.2) and Lemma L, for any `rho <= z_0`,

    e^{q_i x} f_F(s, x) = Acal + Ecal,      Acal = (1/(2 pi i)) oint_{|z| = rho} e^{x/z} Lam(z) z^{-2} dz,
    |Ecal| <= (C/S) Aabs,      Aabs = (1/(2 pi)) oint_{|z| = rho} |e^{x/z} Lam(z)| |z|^{-2} |dz| .

By definition `K_beta(x, S) = e^{-q_i x} Acal/Lam(0)` when `rho = z_*` (the integral does not
depend on `rho`). So it suffices to show `Aabs <= C' Acal` with `Acal > 0`. Put
`E(z) = (C(beta, z)/C(beta, 0)) e^{S (I_G - J(beta, z) - ab z)}`, so
`Lam(z)/Lam(0) = e^{S ab z} E(z)`. By Proposition 3(ii) and the holomorphy of `C`,
`log E(z) = c_1 z - S j_2 z^2 + O(|z|^2 + S |z|^3)` on `|z| <= z_0`. We need `delta` so small that
`sqrt(2 delta/ab_min) <= z_0/2` (then `z_* <= z_0/2`) and that `x/Z` is small, see below.

Regime (i), `Z <= Z_0` (a fixed large constant). Take `rho = max(z_*, 1/S) <= C/S`. On the circle
`|x/z| <= Z_0^2`, `|S ab z| <= C` and `|E(z) - 1| <= C/S`. Let `Acal_0` be `Acal` with `E = 1`. It
equals `Lam(0) sqrt(ab S/x) I_1(Z) >= Lam(0) ab S`, because `sqrt(ab S/x) I_1(Z) = ab S
sum_k (Z/2)^{2k}/(k!(k+1)!)`. Also `|Acal - Acal_0| <= C Lam(0) rho^{-1} (1/S) <= C Lam(0)` and
`Aabs <= C Lam(0) rho^{-1} <= C Lam(0) S`. Hence `Acal >= Lam(0)(ab S - C) > 0` and
`Aabs <= C' Acal` for `S` large.

Regime (ii), `Z >= Z_0`. Let `Lamb(z) = x/z + S ab z + log E(z)`, holomorphic on
`|z| <= z_0`, real on the real axis. Its real critical point `rho_s` near `z_*` exists and
`rho_s = z_* (1 + O(sqrt(x/S) + 1/Z))` by the implicit function theorem, since
`Lamb'(z) = -x/z^2 + S ab + O(1 + S|z|)`. Take `rho = rho_s`. For `z = rho e^{i phi}`,

    Re Lamb(z) - Lamb(rho) = (x/rho + S ab rho)(cos phi - 1) + Re[ R(z) - R(rho) ],

with `R = log E`. Since `R` is real on the real axis, `Re[R'(rho)(z - rho)] = R'(rho) rho
(cos phi - 1)`, and `|R''| <= C(1 + S)` gives the remainder bound
`C(1 + S) rho^2 |e^{i phi} - 1|^2 = 2 C(1 + S) rho^2 (1 - cos phi)`. Also
`|R'(rho)| rho <= C(rho + S rho^2)`. Now `S rho^2 ~ x/ab` and `x/rho + S ab rho ~ Z`, and
`x/Z <= sqrt(x/(4 ab S)) <= C sqrt(delta)`. So for `delta` small,
`Re Lamb(z) - Lamb(rho) <= -(Z/2)(1 - cos phi)`. Hence
`Aabs <= Lam(0) rho^{-1} e^{Lamb(rho)} (1/(2 pi)) int e^{-(Z/2)(1 - cos phi)} d phi
<= C Lam(0) rho^{-1} e^{Lamb(rho)} Z^{-1/2}`. For the lower bound write
`Acal = Lam(0) rho^{-1} (1/(2 pi)) int e^{Z lam(phi)} e^{-i phi} d phi` with
`lam(phi) = Lamb(rho e^{i phi})/Z`. The derivatives of `lam` are bounded uniformly in all
parameters, `lam'(0) = 0`, `-lam''(0)` lies in `[1/2, 2]`, and the gap above holds. The proof of
Lemma D.1 of the draft uses nothing else, so it gives
`Acal = Lam(0) rho^{-1} e^{Lamb(rho)} (2 pi Z (-lam''(0)))^{-1/2} (1 + O(1/Z))`, which is positive
and at least `c Aabs`. ∎

### 6.3 From the generalized kernel to the Bessel form, Theorem 2(b)

Two facts on Bessel functions. First, with `z = z_* t` we have
`x/z + ab S z = (Z/2)(t + 1/t)`, so the generating function of the `I_k` gives

    (1/(2 pi i)) oint e^{x/z + ab S z} z^{n-2} dz = z_*^{n-1} I_{n-1}(Z)      (n in Z).      (6.1)

Second, for integer `n >= 1`, `I_n(Z) = (1/pi) int_0^pi e^{Z cos t} cos(n t) dt`, so
`I_n <= I_1` for all `Z > 0`, and `|I_1 - I_n| <= ((n^2 - 1)/(2 pi)) int_0^pi e^{Z cos t} t^2 dt
<= C n^2 I_1(Z)/Z` for `Z >= 1`. We also use `I_0/I_1 <= 1 + 2/Z`.

The reversible case. Here `J` is exactly linear in `z` (Proposition 3(iv)), so
`E(z) = C(beta, z)/C(beta, 0) = 1 + c_1 z + sum_{n >= 2} c_n z^n` with `|c_n| <= C z_0^{-n}`. By
(6.1) the term `c_n z^n` contributes `c_n z_*^n I_{n-1}(Z)/I_1(Z)` relative to the main term
`z_*^{-1} I_1(Z)`. For `n >= 2` this is at most `|c_n| z_*^n`, and the sum over `n >= 2` is
`O(z_*^2) = O(x/T)` since `z_* <= z_0/2`. The term `n = 1` is `c_1 z_* I_0(Z)/I_1(Z)`, which is
`O(z_* + 1/(ab S)) = O(sqrt(x/T) + 1/T)`. With the error `O(1/T)` of 2(a) this proves both
reversible claims of 2(b), for all `0 < x <= delta T`, with no saddle point argument.

The general case, `x <= 1`. Write `E(z) = e^{-S j_2 z^2} (1 + c_1 z + R(z))` with
`|R(z)| <= C(|z|^2 + S |z|^3)`. On `|z| = z_*` the factor `e^{-S j_2 z^2}` has modulus at most
`e^{j_2 x/ab} <= C`. Expanding `e^{-S j_2 z^2} = sum_m (-S j_2 z^2)^m/m!` and using (6.1), the
term `1` gives the relative factor `sum_m (-y)^m/m! I_{2m-1}(Z)/I_1(Z)` with `y = (j_2/ab) x`,
which differs from `e^{-y}` by at most `C sum_{m >= 1} y^m m^2/(m! Z) <= C' x/Z = O(sqrt(x/S))`
when `Z >= 1` (and regime (i) of 6.2 covers `Z <= Z_0`). The term `c_1 z` gives
`O(z_*(1 + 1/Z))`, and `R` gives `O(z_*^2 + S z_*^3) (1 + 2/Z) = O(x/S + x^{3/2} S^{-1/2})`. So
`K_beta = B_beta (1 + O(1/S + sqrt(x/S)))` for `x <= 1`.

The general case, `1 <= x <= delta T`. We use the saddle point evaluation of 6.2 for `Acal` and
for the same integral with `E = 1`, which is `Lam(0) z_*^{-1} I_1(Z)`. Their ratio is
`exp(Lamb(rho_s) - Z) (z_*/rho_s) (-lam''(0) at E = 1 / -lam''(0))^{1/2} (1 + O(1/Z))`. Here
`rho_s/z_* - 1 = O(sqrt(x/S))`, the second derivatives differ by a relative `O(sqrt(x/S))`, and
`Lamb(rho_s) - Z = -(j_2/ab) x + c_1 z_* + O(x^{3/2} S^{-1/2} + x/S)`, because `Z` is the value
of `x/z + S ab z` at its own critical point `z_*` and the shift from `z_*` to `rho_s` changes it
only to second order. Since `1/Z <= C/sqrt(S) <= C sqrt(x/S)` for `x >= 1`, the ratio is
`e^{-(gamma - q_i) x} (1 + O(sqrt(x/T)(1 + x)))`. This proves the general claim of 2(b). ∎

The non-reversible Bessel form is useful only for `x << T^{1/3}`, because of the term
`S j_3 z^3` with `z ~ z_*`, which is of size `x^{3/2}/T^{1/2}`. The generalized kernel has no
such restriction. At `x = alpha_i T` with `alpha_i` small but fixed, its saddle point evaluation
reproduces the exponent `-T I_F(alpha)` exactly, by the Legendre identity of Proposition 3(i),
so 2(a) and the local law of the draft overlap and together cover the face up to its facet.

### 6.4 The discrete form 2(c)

Lemma 1' is exact. Its `K`-th term is `binom(n_i - 1, K - 1)(1 - hq_i)^{n_i - K}` times
`[z^K] P^{(z)}_{N'}(nhat)`. If `[z^K] P^{(z)}_{N'}(nhat)` is replaced by the continuum quantity
`h^{g-1+K} [z^K] Phi(z)(hnhat)`, the sum becomes `h^g f_F` up to the clipped products of the
`i`-runs, and these produce exactly the Laguerre polynomial `B_{n_i}`. The remaining step is a
version of Lemma L for the discrete weighted chain `P^{(z)}_{N'}`, uniform for `|z| <= z_0`,
with error `O(1/T + T^2/N)`. That is Lemma 4.5 of the draft (a term-by-term comparison of runs)
for complex weights. We have not written it. For `g = 1` it is exact, see Section 8.

## 7. Numerical checks

The three chains of Part A. Uniform start. `G = {1, 2}`, `i = 3`, so the line from the edge
`{1, 2}` into the interior is `n = ((N - n_3)/2, (N - n_3)/2, n_3)`, `beta = (1/2, 1/2)`.

### 7.1 The requested discrete check, N = 400, 800 and T = 6, 10

Ratios of the exact probability (dynamic programming over compositions) to three predictions.
`R_cont` uses `h P_{N'}(nhat) B_beta(x, S)`. `R_lat` uses the Laguerre kernel of 2(c). `R_lat2`
uses the Laguerre kernel times the amplitude correction `1 + c_1 z_* I_0(Z)/I_1(Z)`. Source
`08_layer_output3.txt`.

Path `1-2-3`, `ab = 1/2`, `gamma = 1`, `c_1 = 1`.

| N, T | n_3 = 2 | 8 | 32 | N/8 | N/4 |
|---|---|---|---|---|---|
| 400, 6 | 1.347 / 1.357 / 1.005 | 1.406 / 1.413 / 1.012 | 1.615 / 1.617 / 1.035 | 1.759 / 1.757 / 1.050 | 2.146 / 2.137 / 1.090 |
| 400, 10 | 1.196 / 1.239 / 1.012 | 1.285 / 1.322 / 1.024 | 1.557 / 1.575 / 1.060 | 1.723 / 1.731 / 1.079 | 2.138 / 2.126 / 1.123 |
| 800, 6 | 1.340 / 1.345 / 1.002 | 1.369 / 1.373 / 1.005 | 1.477 / 1.480 / 1.017 | 1.750 / 1.749 / 1.045 | 2.131 / 2.127 / 1.085 |
| 800, 10 | 1.197 / 1.219 / 1.005 | 1.241 / 1.261 / 1.010 | 1.386 / 1.400 / 1.026 | 1.698 / 1.701 / 1.061 | 2.095 / 2.089 / 1.104 |

Reversible chain `nu = (1, 2, 4)`, `ab = 3.125`, `gamma = q_3 = 1.6642`, `c_1 = 3.3033`.

| N, T | n_3 = 2 | 8 | 32 | N/4 |
|---|---|---|---|---|
| 400, 6 | 1.112 / 1.241 / 1.015 | 1.265 / 1.390 / 1.045 | 1.696 / 1.802 / 1.122 | 2.656 / 2.697 / 1.259 |
| 400, 10 | 0.888 / 1.218 / 1.038 | 1.103 / 1.449 / 1.115 | 1.703 / 2.034 / 1.285 | 3.057 / 3.218 / 1.521 |
| 800, 6 | 1.142 / 1.208 / 1.007 | 1.220 / 1.285 / 1.018 | 1.454 / 1.513 / 1.052 | 2.560 / 2.580 / 1.204 |
| 800, 10 | 0.982 / 1.159 / 1.014 | 1.095 / 1.273 / 1.041 | 1.389 / 1.561 / 1.105 | 2.723 / 2.793 / 1.320 |

Non-reversible cycle, `ab = 5.182`, `gamma = 3.418` (`q_3 = 3`), `c_1 = 3.996`.

| N, T | n_3 = 2 | 8 | 32 | N/4 |
|---|---|---|---|---|
| 400, 6 | 1.005 / 1.193 / 1.009 | 1.180 / 1.354 / 1.048 | 1.691 / 1.812 / 1.164 | 3.144 / 3.138 / 1.524 |
| 400, 10 | 0.725 / 1.184 / 1.029 | 0.956 / 1.423 / 1.118 | 1.689 / 2.080 / 1.350 | 4.053 / 4.090 / 2.005 |
| 800, 6 | 1.061 / 1.161 / 1.003 | 1.153 / 1.247 / 1.018 | 1.415 / 1.493 / 1.068 | 3.041 / 3.038 / 1.475 |
| 800, 10 | 0.869 / 1.129 / 1.009 | 0.995 / 1.250 / 1.042 | 1.333 / 1.560 / 1.130 | 3.666 / 3.682 / 1.805 |

Reading. At `T = 6, 10` the one-term ratios are far from `1`. The deviation is the amplitude
term, which is `c_1/(ab S)` in the few-visit regime (for the path `2/T`, so `1.33` at `T = 6`
and `1.2` at `T = 10`) and `c_1 z_*` in the many-visit regime. The two-term lattice ratio
`R_lat2` is within `0.2` to `4` percent at `n_3 = 2` for all three chains and all four `(N, T)`.
At `n_3 = 8` it is within `0.5` to `12` percent, and the larger values occur where `n_3` is beyond
the few-visit range `n_3 <~ N/(ab T^2)` (which is `1.3` for the reversible chain at `N = 400`,
`T = 10`). The column `N/4`
is not in the layer (`alpha_3 = 1/4`), and the Bessel form is not expected to hold there. The
Laguerre kernel is clearly better than the continuum kernel when `ab T^2/N` is not small (the
reversible and non-reversible rows at `T = 10`, `N = 400`, where `ab T^2/N` is `0.8` and `1.3`).
For instance the continuum ratio from 7.2 below for the reversible chain at `T = 10`,
`x = 0.05` is about `1.18`, and `R_lat = 1.218` while `R_cont = 0.888`.

### 7.2 Continuum ratios at larger T

Source `08_layer_output.txt` (Part C) and `08_layer_output2.txt` (Part F). The exact continuum
density from (2.2) divided by `f_G(s)` times the kernel, for `x` across the regimes. One-term
(Bessel) and two-term (with `1 + c_1 z_* I_0/I_1`).

Path, one-term.

| T | x = 1/T | 0.3 | 1 | 3 | T/10 | T/4 |
|---|---|---|---|---|---|---|
| 6 | 1.4338 | 1.5083 | 1.8644 | 3.0689 | 1.6650 | 2.1170 |
| 10 | 1.2533 | 1.3444 | 1.5944 | 2.2132 | 1.5944 | 2.0538 |
| 80 | 1.0309 | 1.0957 | 1.1722 | 1.3053 | 1.5339 | 1.9909 |

Two-term, at `x = 1/T, 1, 3, 10, T/10, T/4`.

| chain | T = 40 | T = 160 | T = 320 |
|---|---|---|---|
| path | 1.0003, 1.0103, 1.0284, 1.0901, 1.0371, 1.0901 | 1.00002, 1.0028, 1.0080, 1.0243, 1.0376, 1.0913 | 1.000005, 1.0014, 1.0042, 1.0128, 1.0377, 1.0916 |
| reversible | 1.0006, 1.0181, 1.0487, 1.1511, 1.0633, 1.1511 | 1.00004, 1.0050, 1.0138, 1.0412, 1.0631, 1.1510 | 1.00001, 1.0026, 1.0072, 1.0220, 1.0631, 1.1509 |
| non-reversible | 1.0008, 1.0699, 1.3317, 4.38, 1.524, 4.38 | 1.00006, 1.0310, 1.1510, 2.145, 4.39, 230 | 1.00001, 1.0211, 1.1041, 1.736, 18.0, 45312 |

Reading. For the two reversible chains the two-term error at fixed `x` halves when `T` doubles,
which is the `O((1 + x)/T)` of 2(b). At `x = T/10` and `T/4` it tends to a constant, as it must
outside the layer. For the non-reversible chain the error at fixed `x` falls like `T^{-1/2}`
(`0.0310` to `0.0211` at `x = 1` from `T = 160` to `320`), and it grows with `T` at
`x = T/10` and `T/4`. That is the term `x^{3/2} T^{-1/2}` of 2(b). Without the correction
`gamma - q_3 = 0.418` the one-term ratio at `x = 3`, `T = 80` is `0.470` instead of `1.648`, and
at `x = T/4` it is `0.008`. So `gamma` is needed and its value is right.

### 7.3 The generalized kernel

Source `08_layer_output2.txt` (Part G). The exact continuum density divided by
`e^{-q_i x} (1/(2 pi i)) oint e^{x/z} Lam(z) z^{-2} dz`, where `Lam` is the leading form of
`Phi(z)` (here the large-argument form of the closed two-state density, which is exactly
`S^{-1/2} C(beta, z) e^{-S J(beta, z)}` up to the constant). This tests 6.2, the deduction of
2(a) from Lemma L, for `x` from `0.01/T` to `T/4`.

| chain | T = 10 | T = 40 | T = 160 | T = 320 |
|---|---|---|---|---|
| path | 0.9780 to 0.9872 | 0.9951 to 0.9969 | 0.9988 to 0.9992 | 0.99939 to 0.99961 |
| reversible | 0.9868 to 0.9887 | 0.9969 to 0.9972 | 0.99923 to 0.99931 | 0.99961 to 0.99966 |
| non-reversible | 0.9919 to 0.9928 | 0.9979 to 0.9982 | 0.99948 to 0.99955 | 0.99974 to 0.99978 |

The ranges are over all `x` in the table, up to `x = T/4`. The error is `O(1/T)` and uniform in
`x`, including the non-reversible chain. This is 2(a).

## 8. Comparison with the near-vertex theorem

The near-vertex theorem of the draft (Theorem 6.2 with Lemma 6.1) is for `Q = J - dI` with the
uniform start and the composition `(b, a_1, ..., a_l)`. Take `l = 1`. Then `F = {1, 2}`,
`G = {1}`, `i = 2`, `n = (b, a)`, `q_12 = q_21 = 1`, `q_1 = q_2 = d - 1`, `p = 1 - (d - 1)h`,
`u = h/p`. Lemma 1' with `g = 1` is exact and gives

    P_N(b, a) = sum_K binom(a-1, K-1) (1 - hq_2)^{a-K} [z^K] (mu_1 + z h mu_2)(1 + z h)(1 - h q_1 + z h^2)^{b-1}.

Its main part, from `mu_1 . 1 . (1 - hq_1 + zh^2)^{b-1}`, is

    mu_1 p^{N-1} sum_K binom(a-1, K-1) binom(b-1, K) u^{2K}.

With `binom(b - 1, K) = (b^K/K!)(1 + O(K^2/b))` this is `mu_1 p^{N-1} B_a(b u^2)`, which is the
leading term of the draft's `S_{(b,a)}(u)`, since `P_N(n) = mu_1 p^{N-1} S_n(u)`. The draft's
exact formula `S_{(b,a)}(u) = (1 - u)^{|a|} E[B(v X)]` with `X = Gamma_2 + sum_{j < b} Z_j E_j`
is the probabilistic form of the same sum. The Bernoulli variables `Z_j` choose which of the
`b - 1` steps of the vertex run carry an excursion, which is the factor `binom(b - 1, K)`. The
shape `2` of the gamma variable carries the start and end terms, which are the `I_0` terms of
Proposition 2. So the near-vertex law for `l = 1` is the discrete pair-face case of Lemma 1', and
its leading kernel is our lattice kernel with `ab = q_12 q_21 = 1`, `S = hb`, `x = ha` and
`gamma = q_2`.

The two theorems live in different regimes. In Theorem 6.2, `u ~ b^{-1/2}`, so `T ~ sqrt N` and
the lattice parameter `w = b u^2 = ab S h` is of order one. Lemma 6.1 bounds
`B_a(w)/(w I(aw))` between `1 - w/2` and `1`, so the Laguerre kernel cannot be replaced by the
Bessel kernel there, and the continuum layer (which needs `T^2/N -> 0`) does not apply. When
`T^2/N -> 0`, the same Lemma 6.1 gives `B_a(w) = w I(aw)(1 + O(w))` uniformly in `a`, and
`w I(a w) = b h^2 I(a b h^2) = h S I(S x) = h sqrt(S/x) I_1(2 sqrt(S x))`, which is our Bessel
kernel with `ab = 1`. The error terms correspond as well. The draft's
`epsilon = sqrt((|a| + 1)/b)` is our `1/S + sqrt(x/S)` with `x/S = a/b` and `1/S = 1/(bh)`, which
is of order `b^{-1/2}` at `u ~ b^{-1/2}`. So at the level of the kernel the near-vertex theorem is
the special case `|F| = 2`, `G` a vertex, and Lemma 6.1 is exactly the uniform comparison of the
lattice and continuum layers of Theorem 2(c).

For `l >= 2` the draft's product `prod_r B_{a_r}` is a corner of codimension `l`, outside a single
facet layer. A chained excursion `1 -> r -> r' -> 1` has one switch fewer but one place fewer
than two separate excursions, so it is smaller by a factor of order `1/(bh) = 1/S`, and to
leading order the corner is a product of independent layers. For the complete graph the product
is exact because of the refresh structure of `eq:simplex-balance-integral`.

## 9. Status of each deliverable

(1) The statement is Theorem 2 in Section 1, with uniformity over `beta` in compact subsets of
the open facet, `T >= T_0`, `0 < x <= delta T` (all `x` for pair faces), and the stated errors.

(2) The run expansion restricted to `i` is Lemma 1 and Lemma 1', proved. The series is
`sum_K x^{K-1}/(K-1)! [z^K] Phi(z)(s)`, and `[z^K] Phi(z)(s) ~ f_G(s)(ab S)^K/K!` in the
few-visit regime. The powers `q_i^K` of the heuristic cancel. The uniform estimate of the
insertion weights is done through the contour formula (2.2) and Lemma L, not term by term.

(3) The constants for non-reversible `Q` are `ab = (c^- . l_beta)(c^+ . r_beta)` and
`gamma = q_i + (ab/2)(pi^out - pi^in)^T L_beta^+ (pi^out - pi^in)`, proved as the coefficients of
the facet expansion of `I_F` (Proposition 3). The prefactor is `c = 1` and the first amplitude
correction is `c_1`, with a closed form in the reversible case.

(4) Numerics in Section 7. The requested ratios at `N = 400, 800`, `T = 6, 10` are in 7.1. They
are dominated by the amplitude term at these `T`, and the two-term lattice ratio is within a few
percent in the few-visit regime. The asymptotic rates are confirmed in 7.2 and 7.3.

(5) The near-vertex theorem is the pair-face case with `G` a vertex, at the level of the kernel,
and Lemma 6.1 is the lattice-continuum comparison of 2(c) (Section 8).

(6) The first unresolved implication is Lemma L, the local law for `M(z)` uniformly in complex
`|z| <= z_0`, for `|G| >= 2`. Its proof outline in 6.1 uses only the torus representation with
complex weights and a complex-Hessian version of Lemma D.1. It is not yet written out in full.
For the discrete form 2(c) the second missing step is the discrete analog of Lemma L (Lemma 4.5
of the draft with complex weights). The strongest statements proved without hypothesis are
Lemma 1, Lemma 1', Proposition 2 (pair faces, all `x`, explicit bound), Proposition 3 (exact
Legendre identity and facet expansion of the rate with `ab` and `gamma` for every irreducible
`Q`, exact in the reversible case), and Proposition 4 (prefactor matching for reversible `Q`).
Theorem 2(a) and (b) are proved from Lemma L in 6.2 and 6.3.

Status. Proved under a stated hypothesis. Pair faces (Proposition 2), the exact representation
(Lemmas 1 and 1'), the constants (Proposition 3) and the reversible prefactor matching
(Proposition 4) are proved. Theorem 2(a) and 2(b) for `|F| >= 3` are proved assuming Lemma L
(complex-parameter local law on the facet), whose proof is outlined in 6.1 but not written in
full. Theorem 2(c) additionally needs the discrete analog of Lemma L.
