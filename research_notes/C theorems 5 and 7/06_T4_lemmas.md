# Route T4. The lemmas Theorem 4 still owes

Base checkpoint `6add913`. Date October 24, 2026.

Inputs read. `00_targets.md` (Target 3) and `07_T4_literature.md` of this folder.
`research_notes/Paper C and F plan review/cut_transpose.py` and its output in
`outputs_2026-10-23.md`. Sections 4.1, 4.2, 5.3 and 7.1 of
`reports/Paper C and F plan review - 2026-10-23.md`. `kagey-problems/problem131/paperC/sec_secondorder.tex`
(Definition 4.1, Proposition 4.2, Theorems 4.4 and 4.6, Proposition 4.9, and the directed 3-cycle
`prop:threecycle`), `sec_firstorder.tex` (the uniform upper bound `lem:upper` and first-order
selection `thm:first`), and the definition of faces `def:faces` in `sec_model.tex`. Draft results
without a number fixed by `00_targets.md` are cited by their LaTeX labels. `research_notes/Occupation novelty and compact advances/11_C_ready_to_draft_outline.md`
Sections 1 to 3 (C-P1 to C-P3, C-I1 and the suppression lemma). Kim and Landim, arXiv:2412.13515v2,
Section 5, read from the arXiv HTML page (statements paraphrased below, not quoted).

Scripts and outputs written by this route.

- `06_amplitudes.py`, output `06_amplitudes_output.txt`. Items 4b and 4d.
- `06_exposure.py`, output `06_exposure_output.txt`. Item 4a.

Both run with `py -I` from this folder.

## 0. Notation and two inputs

We follow `00_targets.md`. `Q` is an irreducible generator on `V`, `|V| = d`, `q_i = -q_ii`,
`w_ij = q_ij q_ji`, and `A = -Q`. For a face `F` we write `A_F` for the principal block of `A` and
`lambda_F(v)` for the smallest real eigenvalue of `A_F - diag(v_F)`. The draft uses `A_F` for the
off-diagonal part of `Q_F` (line 36 of `sec_model.tex`). In this note `A_F` always means `-Q_F`.
A face is irreducible when the switching graph on it is strongly connected. The start `mu` has full
support, so every irreducible face satisfies (H). For a reducible face `G`, `lambda_G(v)` is the
smallest of the numbers `lambda_C(v)` over its strongly connected components `C`. This is again the
smallest real eigenvalue of the block triangular matrix `A_G - diag(v_G)`.

The score of an admissible face is `Phi(G) = |G| - 1 + tau lambda_G(v)`. A point `(tau, v)` lies in
the strict winning region of `G` when `Phi(G) < Phi(G')` for every admissible `G' != G`.

**Input I1 (controlled score law).** For every admissible face `G`, every fixed field and `tau` in a
compact subset of `(0, infinity)`,

    log max_{supp n = G} Pr_mu(n) e^{T v.n/N} = -Phi(G) log N + O(log log N).

For irreducible `G` this is C-P3 of outline 11. For reducible `G` we only need the upper bound, and
it follows from `lem:upper` of the draft as follows. For a component `C` put
`theta = q - v - lambda_C(v) 1`. Then `A^off_C - diag theta = Q_C + diag v_C + lambda_C(v) I` has
Perron root `0`, so `theta` lies in `V_C`, and `lem:upper` gives
`P(n) e^{h v.n} <= C h^{|C|-1} e^{-T lambda_C(v) + C T^2/N}` for a block of composition `n` in `C`.
The block argument of `thm:first`(ii) then multiplies the blocks and the switches. So the upper half
of I1 holds for every admissible face, uniformly for `v` in a compact set. On a strict winning region
the exact maximizing support is that face for all large `N`, because there are finitely many faces
and a fixed gap in `Phi` beats `O(log log N)`.

**Input I2 (Perron-branch lemma).** Section 5.3 of the plan review. If `lambda_F` is known on a
nonempty open set of `R^F`, then `R_F(w) = det(A_F - diag w)` is known, hence every principal minor
of `A_F`, hence `lambda_F` on all of `R^F`. The proof there is complete and we do not repeat it.

Two elementary facts are used throughout. (P1) If `B` is Metzler and `u > 0`, then the Perron root
of `B` is at most `max_i (Bu)_i / u_i` (Collatz and Wielandt, applied to `B + cI >= 0`). (P2) For
irreducible `F` and a proper subset `H`, `lambda_H(v) > lambda_F(v)`. For `H = {i}` this is the
display `q_i - v_i - lambda_F(v) = sum_{j in F, j != i} q_ij r_j(v)/r_i(v) > 0` of C-P3. For general
`H` it is the strict monotonicity of the Perron root of an irreducible Metzler matrix under passage
to a proper principal submatrix (Berman and Plemmons, Chapter 2).

## 1. Item 4a. Exposure of `lambda_F`

### 1.1 What is proved and what is not

We prove that every irreducible face `F`, including `F = V`, shares a boundary of two strict winning
regions with a proper subface `G` on a nonempty open set of `(tau, v)`. Along that boundary
`lambda_F(v) = lambda_G(v) - (|F| - |G|)/tau`. By induction on `|F|` and input I2 this traces
`lambda_F` on an open set of fields for every irreducible `F`. This is all that Theorem 4 needs.

The target asks for more. It asks that the partner be a singleton `{i}`. We prove an exact criterion
for that (Proposition 1.6), we prove it for every face whose only irreducible proper subsets are
singletons (pairs, directed cycles, and the sparse faces of Section 1.5), and we verify the criterion
numerically on random dense and sparse faces with `d = 3, 4`. We do not have a proof of the singleton
version for a general irreducible face with `|F| >= 3`. The first unresolved implication is stated in
Section 1.5. The descent version makes it unnecessary for Theorem 4.

### 1.2 The suppression lemma for a non-reversible generator

The reversible proof in outline 11 uses the Schur bound for the symmetric matrix `S`. That bound is
not available here, so we use (P1).

**Lemma 1.1 (suppression).** Let `F` be a nonempty face, let `K` be a compact subset of `R^F` and let
`eta > 0`. There is `M_0` such that for `M >= M_0`, every `v` with `v_F in K` and `v_j = -M` for
`j` outside `F`, and every face `G` that is not contained in `F`, we have
`lambda_G(v) >= lambda_{G cap F}(v) - eta` when `G cap F` is nonempty, and
`lambda_G(v) >= M` when `G cap F` is empty.

*Proof.* Put `P = G cap F`, `S = G \ F`, and `B = Q_G + diag(v_G)`. The Perron root of `B` is
`-lambda_G(v)`. If `P` is empty, every row of `B` has off-diagonal sum at most `q_s` and diagonal `-q_s - M`, so
the row sums are at most `-M`, and (P1) with `u = 1` gives `lambda_G >= M`. Now let `P` be nonempty and write
`rho_P = -lambda_P(v)`. Let `J_P` be the matrix with ones off the diagonal of `P`. For `eps_0 > 0` the
matrix `Q_P + diag(v_P) + eps_0 J_P` is irreducible and Metzler, so it has a positive Perron vector
`x`. Its Perron root decreases to `rho_P` as `eps_0` decreases to `0`, and it is continuous in `v_P`.
By Dini's theorem we may fix `eps_0` so that this root is at most `rho_P + eta/2` for all `v_F` in
`K`. We normalize `max x = 1`, and the minimum `x_min` of `x` over `K` is positive by continuity and
compactness. We test (P1) with `u = x` on `P` and `u = eps` on `S`. For `p` in `P`,

    (Bu)_p <= ((Q_P + diag v_P) x)_p + eps q_max <= (rho_P + eta/2) x_p + eps q_max <= (rho_P + eta) x_p

once `eps <= eta x_min/(2 q_max)`. For `s` in `S`,

    (Bu)_s <= sum_p q_sp x_p + eps (sum_{s' in S} q_ss' - q_s - M) <= q_max - eps M <= (rho_P + eta) eps

once `M >= q_max/eps + |rho_P| + eta`, which holds uniformly on `K`. So the Perron root of `B`
is at most `rho_P + eta`, that is `lambda_G(v) >= lambda_P(v) - eta`. ∎

**Corollary 1.2.** Let `m_F(tau, v)` be the least score among the irreducible nonempty subsets of
`F`. Fix a compact `tau`-interval `[tau_-, tau_+]` in `(0, infinity)` and a compact `K`. For `M` large,
every admissible `G` not contained in `F` has `Phi(G) >= m_F(tau, v) + 1/2` on `[tau_-, tau_+] x K`.

*Proof.* Take `eta = 1/(2 tau_+)` in Lemma 1.1. If `P = G cap F` is nonempty, `|G| - 1 >= |P|`,
and `lambda_P = lambda_C` for a component `C` of `P`, which is an irreducible subset of `F`. So
`Phi(G) >= |P| + tau lambda_C - 1/2 >= 1 + Phi(C) - 1/2 >= m_F + 1/2`. If `P` is empty, `Phi(G)` is
at least `tau_- M`, which exceeds `m_F + 1/2` for `M` large because `m_F` is bounded on
the compact set. ∎

Reducible faces inside `F` never win either. If `H` is reducible with a component `C` attaining
`lambda_H`, then `Phi(H) = |H| - 1 + tau lambda_C > Phi(C)`. So only irreducible faces can be strict
winners, and only irreducible faces need lower bounds in I1.

### 1.3 Exposure by descent

Fix an irreducible `F` with `k = |F| >= 2`. Put `v_j = -M` off `F`. For an irreducible proper subset
`H` of `F` (singletons included) define

    rho_H(v) = (k - |H|) / (lambda_H(v) - lambda_F(v)).

By (P2) the denominator is positive, and `rho_H` is real-analytic on all of `R^F`, because the Perron
roots of irreducible Metzler matrices are simple. We have `Phi(F) < Phi(H)` exactly when
`tau > rho_H(v)`.

**Lemma 1.3 (generic partner).** If `H_1 != H_2` are irreducible proper subsets of `F`, then
`rho_{H_1} - rho_{H_2}` is not identically zero. Hence the set `E` of `v_F` at which the maximum of
`rho_H(v)` over `H` is attained by two or more subsets is closed and nowhere dense in `R^F`.

*Proof.* After renaming we may pick `j` in `H_1 \ H_2`. Take `v = t e_j` and let `t` tend to
infinity. The field vanishes on `H_2`, so `lambda_{H_2}` stays fixed, while
`lambda_F <= lambda_{{j}} = q_j - t` tends to minus infinity. So `rho_{H_2}` tends to `0`. On the
other side `lambda_{H_1} <= q_j - t`. The rows of `Q_F + diag v` sum to at most `max_i v_i = t`, so
(P1) with `u = 1` gives `lambda_F >= -t`, and `lambda_{H_1} - lambda_F <= q_j`. Hence
`rho_{H_1} >= (k - |H_1|)/q_j > 0` for all large `t`. The two functions differ at large `t`. A nonzero real-analytic function on `R^F` has a closed
nowhere dense zero set, and `E` lies in a finite union of such sets. ∎

**Theorem 1.4 (exposure by descent).** Let `F` be irreducible with `k >= 2`, and let `v^0` be a field
on `F` outside `E`. Let `G` be the unique maximizer of `rho_H(v^0)` and put
`tau_1(v) = rho_G(v)`. There are an open neighbourhood `U` of `v^0` in `R^F`, numbers `delta > 0`
and `M_0`, such that for `M >= M_0` and the field `(v_F, -M)` the following holds on
`O = {(tau, v_F): v_F in U, |tau - tau_1(v_F)| < delta}`.

1. The set `Sigma = {(tau_1(v_F), v_F): v_F in U}` is a real-analytic hypersurface in `O`.
2. `O` above `Sigma` lies in the strict winning region of `F`, and `O` below `Sigma` lies in the
   strict winning region of `G`.
3. On `Sigma`, `lambda_F(v) = lambda_G(v) - (k - |G|)/tau_1(v)`.

The same holds for `F = V`, where there is nothing to suppress.

*Proof.* Inside `F`, for `tau > max_H rho_H(v)`, every irreducible proper subset scores above `F`.
At `tau = tau_1(v^0)` the face `G` ties with `F`, and every other irreducible proper subset `H` has
`rho_H(v^0) < tau_1(v^0)`, so `Phi(H) > Phi(F)` there. By continuity of the finitely many functions
`rho_H` and `Phi(H)` there are `U`, `delta` and `kappa > 0` with the following properties on the
closure of `O`. `G` is still the unique maximizer of `rho_H(v)`, and every irreducible subset `H` of
`F` other than `F` and `G` has `Phi(H) >= min(Phi(F), Phi(G)) + kappa`. The difference
`Phi(F) - Phi(G) = (k - |G|) - tau (lambda_G - lambda_F)` is negative for `tau > tau_1(v)` and
positive for `tau < tau_1(v)`. So `min(Phi(F), Phi(G)) = m_F(tau, v)` on `O`. The reducible subsets
of `F` lose to their components. Corollary 1.2 with the compact closure of `O` gives `M_0` such that
every face not inside `F` scores at least `m_F + 1/2`. This proves 2. The function `tau_1 = rho_G` is
real-analytic, which proves 1. The tie `Phi(F) = Phi(G)` is the identity in 3. ∎

**Corollary 1.5 (every face is traced).** Suppose the singleton switches have fixed the diagonal
`q_i` up to one additive constant `c`, as in C-I1, so that `lambda_{{i}}(v) = q_i - v_i` is known up
to `c`. Then the boundaries of Theorem 1.4 determine, for every irreducible face `F`, the function
`lambda_F` on all of `R^F` up to the same constant `c`, and `lambda_V(0) = 0` fixes `c`.

*Proof.* Induction on `|F|`. Singletons are the base. Let `|F| >= 2` and assume the claim for all
smaller irreducible faces. Pick `v^0` outside `E`. Its partner `G` is a proper irreducible subset, so
`lambda_G` is known on `R^G` up to `c` by induction. Theorem 1.4 gives `lambda_F` on the open set `U`
up to `c`, through the observed labels `F` and `G` and the observed position `tau_1(v)`. Input I2,
applied to `w -> R_F(w + c 1)`, extends `lambda_F` to all of `R^F` up to `c`. For `F = V` the
generator has `lambda_V(0) = 0`, which fixes `c`. ∎

The observer knows which face is which, because the observable is the exact maximizing support. So
the induction is an algorithm. Choose `v^0` at random on `F`, decrease `tau` from a large value, and
read the first label change and its position.

### 1.4 The singleton reference

**Proposition 1.6 (criterion).** Let `F` be irreducible with `k >= 2` and `i` in `F`. Suppose that a
field `v^0` on `F` satisfies

    (S1) lambda_j(v^0) > lambda_i(v^0) for every j in F \ {i},
    (S2) (lambda_i - lambda_H)(v^0) / (|H| - 1) < (lambda_i - lambda_F)(v^0) / (k - 1)
         for every irreducible H in F with 2 <= |H| <= k - 1.

Then the conclusions of Theorem 1.4 hold with `G = {i}`, and along the boundary
`lambda_F(v) = q_i - v_i - (k - 1)/tau`. Conversely, if `F` and `{i}` share a boundary of strict
winning regions at a point of `Sigma` where no third face ties, then (S1) and (S2) hold there.

*Proof.* (S1) and (S2) say that `rho_{{i}}(v^0) > rho_H(v^0)` for every other irreducible proper
`H`. For a singleton `H = {j}` this reads `(k-1)/(lambda_i - lambda_F) > (k-1)/(lambda_j - lambda_F)`,
which is (S1). For `|H| >= 2` it is (S2) after inverting both sides. So `{i}` is the unique maximizer
of `rho_H(v^0)`, `v^0` is outside `E`, and Theorem 1.4 applies with `G = {i}`. The converse reads the
same inequalities off the tie at `tau_1`. ∎

Geometrically, (S1) and (S2) say that the segment from `(lambda_i, 0)` to `(lambda_F, k - 1)` is an
edge of the lower convex hull of the points `(lambda_H, |H| - 1)`, `H` in `F`.

**Corollary 1.7.** If every irreducible proper subset of `F` is a singleton, then `F` and `{i}` share
a boundary of strict winning regions on an open set for every `i` in `F`. In particular this holds
for every irreducible pair and every directed cycle.

*Proof.* (S2) is empty. Take `v^0` with `v_i - q_i > v_j - q_j` for all `j != i`, which is (S1). ∎

### 1.5 The open part, and why the naive designs fail

For `|F| >= 3` with an irreducible proper subset of size at least 2, the singleton version needs the
following implication, which we have not proved.

> (Open) For every irreducible `F` with `|F| >= 3` there are `i` in `F` and `v` in `R^F` satisfying
> (S1) and (S2).

Two natural designs fail, and the reasons show where the difficulty lies.

- A large field on `i` alone, `v = delta e_i` with `delta` large. Expanding the Schur complement,
  `lambda_i - lambda_H` equals the sum over first-return loops from `i` inside `H`, weighted by
  `delta^{-(length - 1)}`. The shortest loops through `i` dominate. If they lie in a proper subset
  `H`, then `lambda_i - lambda_H` is asymptotic to `lambda_i - lambda_F`, and (S2) fails for that
  `H` because `(|H| - 1)/(k - 1) < 1`. This is the non-reversible form of the reason why C-I1
  suppresses all states but the retained pair.
- A vertex limit `alpha*_F(v) -> e_i`. With `D` the Bregman divergence of the Donsker and Varadhan
  rate, (S1) and (S2) read `D_H > ((k - |H|)/(k - 1)) D(e_i)` for the minimum `D_H` of `D` on the face
  of `H`. Near `e_i` the leading terms of `D` are additive over the coordinates, of size
  `sqrt(w_il alpha_l)`, and (S2) then holds with equality when the terms are equal and fails
  otherwise. The decision is made at the next order, which we have not controlled.

What works in examples is resonance. For a strong pair `{1,2}` with `q_12 = q_21 = L` and weak links to
a third state, putting `v_3` so that `lambda_3` equals the Perron root of the pair makes the full
face gain of order the coupling, while the pairs through `3` gain of order the coupling squared over
`L`. We could not turn this into a general construction, because for a general generator there is no
small parameter that separates the resonant gain from the non-resonant ones.

Numerical evidence, `06_exposure.py` part (1). We maximized the smallest normalized margin of (S1)
and (S2) over `v` and `i` by Nelder and Mead from random starts, on random dense generators, random
sparse generators (a Hamiltonian cycle plus chords) and generators with a strong pair, `d = 3, 4`,
`F = V`. The best margin was positive for all 18 generators, the smallest being `+0.085` (dense,
`d = 4`). The hard case of a strong pair with a one-way loop `2 -> 3 -> 1` also has a positive margin.
Part (2) shows that on sparse faces the descent partner at a random field is very often a singleton,
with a large `tau_1`, and on dense faces it is usually a face of size `k - 1`. Part (3) checks
Lemma 1.1 at `d = 5`, `F = {1,2,3}`. The largest excess `lambda_{G cap F} - lambda_G` is `0.67`,
`0.079` and `0.0080` for `M = 10, 100, 1000`, so it decays like `1/M`, and faces outside `F` have
`lambda_G >= M + 4.1`. The numbers are recorded in
`06_exposure_output.txt`. This is evidence for (Open), not a proof.

## 2. Item 4b. Amplitudes on the fiber

### 2.1 What is fiber-invariant in `K_F(v)`

For the controlled atom the local law and the face maximum of Theorems 4.4 and 4.6 hold with
`I_F(alpha) - v.alpha` in place of `I_F(alpha)`. Its minimizer is the quasi-ergodic law
`alpha*_F(v) = l o r` of `A_F - diag v`, where `r` and `l` are the right and left Perron vectors with
`l.r = 1`. At `alpha*_F(v)` the optimal vector of Definition 4.1 is a multiple of `r`, by the
computation after (4.1) of the draft with `q - v` in place of `q`. So

    K_F(v) = (mu_F . r)(l . 1) * Gamma_F(v),   Gamma_F(v) = (2 pi)^{-(k-1)/2} det(Sigma_{alpha*_F(v)})^{-1/2},

and by Proposition 4.2(a) `Gamma_F(v) = (2 pi)^{-(k-1)/2} det(Hess I_F(alpha*_F(v)))^{1/2}`. We call
`a_F(v) = (mu_F . r)(l . 1)` the amplitude.

**Lemma 2.1.** Let `Q_1` and `Q_2` be irreducible generators whose matrices `-Q_1` and `-Q_2` have the
same principal minors. For every face `F` that is irreducible for `Q_1`, `F` is irreducible for
`Q_2`, and `lambda_F(v)`, `alpha*_F(v)`, `I_F` and `Gamma_F(v)` are the same for both, for every `v`.
So `K^1_F(v) / K^2_F(v) = a^1_F(v) / a^2_F(v)`.

*Proof.* The blocks `A^1_F` and `A^2_F` have the same principal minors, so
`det(t I - A_F + diag v)` is the same polynomial in `(t, v)` for both. Irreducibility of `F` for
`Q_2` follows from Lemma 5.1 of Al Ahmadieh (a matrix is irreducible exactly when
`det(diag(x) + A)` is an irreducible polynomial), applied to the block. So `lambda_F(v)` agrees for all `v`. The
Donsker and Varadhan formula `lambda_F(v) = min_{alpha} [I_F(alpha) - v.alpha]` says that
`-lambda_F` is the Legendre transform of the convex lower semicontinuous function `I_F` on the
simplex. So `I_F` is the Legendre transform of `-lambda_F` and is the same for both. Then its Hessian,
its minimizer `alpha*_F(v)` after the tilt, and `Gamma_F(v)` agree. ∎

A second way to see `Gamma_F` is Proposition 4.9(b). The product `prod(rho - lambda_F)` is spectral,
and `f_ij = l_i q_ij r_j` has symmetrization `f + f^T` invariant under transposition and diagonal
similarity. The script checks Definition 4.1 against Proposition 4.9(b) to relative error
`2.0e-14`, and checks that `lambda_F`, `alpha*_F` and `Gamma_F` agree across `{Q, Q*, Q'}` to
`3.4e-14`, on all irreducible faces and four fields.

So everything reduces to the amplitude. Since `l_i r_i = alpha_i` is fiber-invariant, the amplitude
is `a_F = (sum_i mu_i r_i)(sum_i alpha_i / r_i)`, a function of the ray of `r` alone.

### 2.2 Time reversal

Put `D = diag(pi)`. Then `A* = D^{-1} A^T D`, and on a face `A*_F = D_F^{-1} A_F^T D_F`. If
`(A_F - diag v) r = lambda r` and `l^T (A_F - diag v) = lambda l^T`, then

    r* = D_F^{-1} l,    l* = D_F r,    l*.r* = l.r = 1,

and

    a*_F(v) = (mu_F . D_F^{-1} l)(pi_F . r)   against   a_F(v) = (mu_F . r)(l . 1).

At `mu = pi` the two agree on every face and every field. This is not a defect of the second-order
term. It is exact.

**Proposition 2.2 (stationary obstruction).** With `mu = pi`, the law of the occupation vector `n` is
the same under `Q` and under `Q*`, for every `N` and `T`. Hence no observable built from occupation
counts separates `Q` from `Q*` under the stationary start.

*Proof.* `P = I + hQ` has stationary law `pi`, and `P* = D^{-1} P^T D = I + h Q*`. For a path
`x_1 ... x_N` we have `pi_{x_1} prod_t P(x_t, x_{t+1}) = pi_{x_N} prod_t P*(x_{t+1}, x_t)`. Reversal
is a bijection of paths that keeps the composition. Summing over paths with composition `n` gives the
claim, and the factor `e^{T v.n/N}` does not see the order. ∎

### 2.3 The cut-transpose acts blockwise

Let `X` be a cut of `A`, `Y = V \ X`, and write `A[X,Y] = -a b^T`, `A[Y,X] = -c d^T` with
`a, b, c, d >= 0` and nonzero. The canonical Z-preserving cut-transpose of `07_T4_literature.md`,
section (i), is `A' = [[A_X, -a c^T], [-b d^T, A_Y^T]]`.

**Lemma 2.3 (flux balance).** For every `v`, the Perron vectors of `A - diag v` satisfy
`(l_X . a)(b . r_Y) = (l_Y . c)(d . r_X)`.

*Proof.* Take the `X` rows of `(A - diag v) r = lambda r` and pair them with `l_X`. Take the `X`
columns of `l^T (A - diag v) = lambda l^T` and pair them with `r_X`. Both give
`l_X^T (A_X - diag v_X) r_X - lambda l_X . r_X`, once as `(l_X . a)(b . r_Y)` and once as
`(l_Y . c)(d . r_X)`. ∎

**Lemma 2.4 (Perron vectors of the cut-transpose).** Put `s = (b . r_Y)/(c . l_Y) = (d . r_X)/(a . l_X)`.
Then `A' - diag v` has the same `lambda` with

    rho = (r_X, s l_Y),    ell = (l_X, s^{-1} r_Y),    ell . rho = l . r.

*Proof.* The `X` rows of `(A' - diag v) rho` are `(A_X - diag v_X) r_X - a (c . s l_Y)`, and
`s (c . l_Y) = b . r_Y`, so they equal `lambda r_X`. The `Y` rows are
`-b (d . r_X) + s (A_Y^T - diag v_Y) l_Y`. The `Y` columns of the left equation for `A` give
`(A_Y^T - diag v_Y) l_Y = lambda l_Y + (l_X . a) b`, so the `Y` rows equal
`lambda s l_Y + b (s (l_X . a) - d . r_X) = lambda s l_Y`. The left vector is checked the same way,
with `s^{-1}`. The two expressions for `s` agree by Lemma 2.3. ∎

The normalized generator is `Q' = -H^{-1} A' H` with `H = diag(h)` and `h` the positive null vector of
`A'`. At `v = 0` we have `r = 1` and `l = pi`, so Lemma 2.4 gives

    h = (1_X, s_0 pi_Y),    s_0 = (b . 1)/(c . pi_Y) = (d . 1)/(a . pi_X).

The script confirms `h/h_1 = (1, 1, 1.190476, 1.619048) = (1, 1, s_0 pi_3, s_0 pi_4)`. Conjugating
by `H` and writing `sigma(v) = s(v)/s_0`, the Perron vectors of `-Q' - diag v` are

    r' = (r_X, sigma D_Y^{-1} l_Y),    l' = (l_X, sigma^{-1} D_Y r_Y),    D_Y = diag(pi_Y).

So `Q'` is `Q` on the `X` coordinates and `Q*` on the `Y` coordinates, glued by the scalar `sigma(v)`.
On the killed blocks this is literal. `Q'_X = Q_X` and `Q'_Y = Q*_Y` (the script finds
`max|Q'_XX - Q_XX| = 2e-16` and `max|Q'_YY - Q*_YY| = 5e-15`). The same computation applies to
any face `F` that meets both `X` and `Y` and is irreducible, with `a, b, c, d` restricted to `F`,
the Perron vectors of `A_F - diag v_F` and the same `h` restricted to `F`.

**Corollary 2.5 (amplitudes of the cut-transpose).** With `l.r = 1` for `Q`,

    a_F(Q)  = (mu_X . r_X + mu_Y . r_Y)(l_X . 1 + l_Y . 1),
    a_F(Q*) = (mu_X . D_X^{-1} l_X + mu_Y . D_Y^{-1} l_Y)(pi_X . r_X + pi_Y . r_Y),
    a_F(Q') = (mu_X . r_X + sigma mu_Y . D_Y^{-1} l_Y)(l_X . 1 + sigma^{-1} pi_Y . r_Y),

all restricted to `F`. In particular the following hold.

1. Faces inside `X`. `Q'_F = Q_F`, so `a_F(Q') = a_F(Q)` for every `mu` and `v`. These faces never
   separate `Q'` from `Q`.
2. Faces inside `Y`. `Q'_F = Q*_F`, so `a_F(Q') = a_F(Q*)`. These faces never separate `Q'` from `Q*`.
3. Faces meeting `Y` in one state `y` (or `X` in one state). The block `A'_F` is a diagonal similarity
   of `A_F` (respectively of `A_F^T`). Indeed with `t = c_y/b_y`, conjugating the state `y` by `t`
   turns `-a b_y` into `-a c_y` and `-c_y d^T` into `-b_y d^T`. So `Q'_F = E^{-1} Q_F E` for a diagonal
   `E` that is `1` on `X cap F`, and `a_F(Q') = (mu_F . E^{-1} r)(E l . 1)`. When `E` is not constant,
   `Q'_F != Q_F`, and the proof of Theorem 2.8 run on the face `F` shows that `a_F(Q') = a_F(Q)` for all
   `v` only for `mu_F` in a proper subspace.
4. The full face at `v = 0`. Every generator has `r = 1` and `l` stationary, so `a_V(0) = mu(V)` for
   every member of the fiber. The full face needs a nonzero field.

**Proposition 2.6 (stationary start and the cut).** Let `mu = pi` and `F = V`. Write
`alpha = pi_X . r_X`, `gamma = l_X . 1`, `beta = pi_Y . r_Y`, `epsilon = l_Y . 1`. Then

    a_V(Q') - a_V(Q) = (alpha - sigma gamma)(beta/sigma - epsilon),

and `a_V(Q*) = a_V(Q)`. The first factor vanishes when `v_X = 0` and the second when `v_Y = 0`. So
under the stationary start `Q'` is separated from `Q` and from `Q*` on the full face exactly at the
fields where both factors are nonzero, and this needs a field that charges both sides of the cut.

*Proof.* Expanding Corollary 2.5 at `mu = pi` gives
`(alpha + sigma epsilon)(gamma + beta/sigma) - (alpha + beta)(gamma + epsilon)`, which is the product
displayed. Suppose `v_Y = 0` and put `G = A_Y`, a nonsingular M-matrix. The `Y` rows of the right
equation and the `Y` columns of the left equation give `r_Y = (d . r_X)(G - lambda)^{-1} c` and
`l_Y = (l_X . a)(G^T - lambda)^{-1} b`. Stationarity `pi^T A = 0` and `A 1 = 0` give
`pi_Y = (pi_X . a) G^{-T} b` and `1_Y = (d . 1) G^{-1} c`. Since `G^{-1}` and `(G - lambda)^{-1}`
commute,

    beta / epsilon = [(pi_X . a)(d . r_X)] / [(l_X . a)(d . 1)] = s / s_0 = sigma,

using the second expressions for `s` and `s_0`. The case `v_X = 0` is the same computation on `X`. ∎

### 2.4 The four-state example

`Q`, `Q*` and `Q'` are those of `cut_transpose.py` (states numbered 1 to 4, `X = {1,2}`). The three
matrices have the same fifteen principal minors to `1.4e-13`. Amplitudes with the non-stationary start
`mu = (0.4, 0.3, 0.2, 0.1)`, from `06_amplitudes_output.txt`. The field only matters on `F`, and a dot
marks a coordinate outside `F`.

| face | field | `a(Q)` | `a(Q*)` | `a(Q')` | `a(Q') - a(Q)` | `a(Q') - a(Q*)` |
|---|---|---|---|---|---|---|
| {1,2,3} | 0 | 0.769626 | 0.938068 | 0.937411 | +1.7e-1 | -6.6e-4 |
| {1,2,3} | (0.5,-1,0.3,·) | 0.754735 | 0.916542 | 0.915539 | +1.6e-1 | -1.0e-3 |
| {1,2,4} | 0 | 0.846979 | 0.657705 | 0.657417 | -1.9e-1 | -2.9e-4 |
| {1,2,4} | (0,0,·,-1) | 0.901711 | 0.712145 | 0.711678 | -1.9e-1 | -4.7e-4 |
| {2,3,4} | 0 | 0.602131 | 0.633800 | 0.635810 | +3.4e-2 | +2.0e-3 |
| {2,3,4} | (·,0,1,-1) | 0.590493 | 0.653957 | 0.656045 | +6.6e-2 | +2.1e-3 |
| {1,3,4} | 0 | 0.726318 | 0.754573 | 0.752399 | +2.6e-2 | -2.2e-3 |
| {1,3,4} | (0,·,1,-1) | 0.714509 | 0.776140 | 0.773839 | +5.9e-2 | -2.3e-3 |
| V | 0 | 1 | 1 | 1 | 0 | 0 |
| V | (1,0,0,0) | 1.024858 | 1.020980 | 1.020685 | -4.2e-3 | -3.0e-4 |
| V | (0,0,1,-1) | 0.985232 | 1.025822 | 1.025824 | +4.1e-2 | +1.9e-6 |
| V | (0.5,-1,0.3,0.8) | 0.971097 | 0.964485 | 0.964269 | -6.8e-3 | -2.2e-4 |
| {1,2} | any | equal | differs by 1e-3 | = `a(Q)` | 0 | about -1.3e-3 |
| {3,4} | any | differs by 0.15 | | = `a(Q*)` | about +0.15 | 0 |

Decision. With this non-stationary start the amplitudes separate `Q'` from `Q` and from `Q*` on all
four triples at every field tested, and on `V` at every nonzero field tested. The separation from
`Q*` is small (of order `1e-3` on the triples, down to `1.9e-6` on `V` at `v = (0,0,1,-1)`), because
`Q'` differs from `Q*` only on the `X` block and the cross blocks, by at most `0.074`. The pair `{1,2}`
inside `X` never separates `Q'` from `Q`, and the pair `{3,4}` inside `Y` never separates `Q'` from
`Q*`, as Corollary 2.5 predicts. With `mu = pi` the full face gives `a(Q) = a(Q*)` at every field,
as Proposition 2.2 forces, while `a(Q') - a(Q) = +5.4e-6` at `v = (0.5,-1,0.3,0.8)` and `-7.8e-6` at
`v = (1,0,1,0)`, matching the product of Proposition 2.6. At `v = (1,0,0,0)`, `(1,-1,0,0)`,
`(0,0,1,-1)` and `(0,0,2,0)` the difference is `0` to rounding, again as Proposition 2.6 says.

We also computed the span `W` of `g_1(v) - g_2(v)`, `g = r (l . 1)`, over 60 random fields on `V`.
For `Q` against `Q*` it has dimension 3 and `W^perp` is spanned by `pi` to six digits. So in this
example every non-stationary start separates `Q` from `Q*` on `V`. For `Q` against `Q'` the smallest
singular value is `4.7e-5` (rounding is of order `1e-15`), so `W = R^4`, and every start, `pi`
included, separates `Q'` from `Q`. The same holds for `Q*` against `Q'`, whose singular values are all
small but nonzero (smallest `2.9e-5`), in line with the direct value `5.4e-6` at `mu = pi`.

### 2.5 The general statement

**Lemma 2.7 (finite fiber).** The set of irreducible generators whose negatives have the same
principal minors as `-Q` is finite.

*Proof.* By Theorem 1.1 of Chatterjee, Ghosh, Gurjar and Raj, every such `-Q'` is diagonally
equivalent to a matrix reached from `-Q` by fewer than `2d` cut-transposes, each along a cut of the
current matrix. There are fewer than `2^d` cuts at each step, so finitely many end matrices, and the
choice of rank-one factors changes the end matrix only by a diagonal similarity (their Remark 2.11).
A diagonal equivalence class `{D B D^{-1}, D B^T D^{-1}}` contains at most two generators, by the sign
lemma and the uniqueness of the normalization in Section 3. ∎

**Theorem 2.8 (amplitudes separate the fiber).** Let `Q_1 != Q_2` be irreducible generators with
the same principal minors of `-Q`. Put `g^k(v) = r^k(v)(l^k(v) . 1)` on the full face, with
`l^k . r^k = 1`, and `W = span{g^1(v) - g^2(v): v in U}` for a nonempty open `U`. Then `W` does not
depend on `U` and `W != 0`. The full-face amplitudes of `Q_1` and `Q_2` agree for all `v` in `U`
exactly when `mu` lies in `W^perp`. Consequently there is a finite union `Z` of proper linear subspaces
of `R^V` such that, for every start `mu` with full support outside `Z`, every two distinct members of
the generator fiber of `Q` have different full-face amplitudes at some field in every open set.
`Z` contains `pi` whenever the fiber contains `Q*` and `Q` is not reversible.

*Proof.* Each `g^k` is real-analytic on `R^V`, so the span over an open set equals the span over
`R^V`. The amplitude is `a^k(v) = mu . g^k(v)`, which gives the equivalence with `W^perp`. Suppose
`W = 0`. Then `g^1 = g^2` on `R^V`, so `r^1(v)` and `r^2(v)` are proportional, and since the two
matrices share `lambda_V(v)` we get `(A_1 - A_2) r(v) = 0` for every `v`. Take `v = t e_j` and let `t`
tend to infinity. Then `lambda_V <= q_j - t` tends to minus infinity, and for `i != j` the `i`-th row of
the eigen-equation gives `(q_i - lambda_V) r_i <= q_max max(r)`, so `r_i / max(r)` tends to `0`. So
`r(t e_j)/max r` tends to `e_j`, and `(A_1 - A_2) e_j = 0` for every `j`. Hence `A_1 = A_2`, a
contradiction. So `W != 0` and `W^perp` is proper. Lemma 2.7 makes the union over pairs finite.
Proposition 2.2 puts `pi` in `W^perp` for the pair `(Q, Q*)`. ∎

How the data see the amplitudes. The second-order position of the boundary between `F` and its descent
partner `G` determines `log K_F(v) - log K_G(v)` along `Sigma`. This needs the crossing equation of
Theorem 4.7 for the controlled atom, which is item (i) of Target 1 (route T5-A). With `K_{{i}} = mu_i`
and the induction of Corollary 1.5, the data determine `K_F(v)/mu_i` on an open set, hence on `R^F` by
analyticity, for every irreducible `F`. By Lemma 2.1 this is the amplitude up to a known factor. So
Theorem 2.8 turns into a statement about the observable, conditional on Target 1 (i).

The paper should therefore not say "a non-stationary start separates the fiber". The correct
statements are these. A non-stationary start is necessary for `Q` against `Q*` (Proposition 2.2).
A start off a finite union of proper subspaces is sufficient for the whole fiber (Theorem 2.8). For a
cut-transpose the stationary start may already separate, through fields charging both sides of the
cut (Proposition 2.6 and the example).

## 3. Item 4c. Normalization and reducible fiber points

**Lemma 3.1 (same spectrum).** If `B` has the same principal minors as `-Q`, then `B` and `-Q` have
the same characteristic polynomial.

*Proof.* `det(t I - B) = sum_{m=0}^{d} (-1)^m t^{d-m} E_m(B)` with `E_m(B)` the sum of the principal
minors of order `m`. ∎

**Lemma 3.2 (sign lemma).** If `C` is irreducible and Metzler, `D` is real diagonal and invertible,
and `D C D^{-1}` is Metzler, then all `d_i` have one sign.

*Proof.* Otherwise strong connectivity gives an arc `i -> j` with `d_i d_j < 0`, and
`(D C D^{-1})_ij = d_i c_ij / d_j < 0`. ∎

**Proposition 3.3 (the normalization).** Let `B` be a Z-matrix with the same principal minors as `-Q`,
and suppose `C = -B` is irreducible. There is a positive diagonal `D`, unique up to a positive scalar,
such that `D^{-1} C D` is a generator. No diagonal similarity with mixed signs gives a generator.

*Proof.* By Lemma 3.1 the spectrum of `C` is that of `Q`. So the spectral abscissa of `C` is `0`.
Perron and Frobenius for the irreducible nonnegative matrix `C + sI` give a simple real eigenvalue `0`
of `C` with an eigenvector `x > 0`, unique up to scaling. With `D = diag(x)`,
`(D^{-1} C D) 1 = D^{-1} C x = 0`, and the off-diagonal entries `c_ij x_j / x_i` stay nonnegative. So
`D^{-1} C D` is a generator, and it is irreducible because it has the pattern of `C`. If `D' > 0` is
diagonal and `D'^{-1} C D'` has zero row sums, then `C (D' 1) = 0` with `D' 1 > 0`, so `D' 1` is a
multiple of `x`. A generator is Metzler, so Lemma 3.2 excludes mixed signs, and a negative scalar
gives the same matrix as a positive one. ∎

The proposition uses the spectral abscissa `0`, which comes from Lemma 3.1. Without it no diagonal
similarity could produce a generator, because a generator has `0` in its spectrum.

**Lemma 3.4 (no reducible fiber points).** Every real matrix `B` with the same principal minors as
`-Q` is irreducible. In particular no reducible generator, and no reducible Z-matrix, lies in the
fiber of `-Q`.

*Proof.* Suppose `B` is reducible. Then there is a proper nonempty `C` with `B[V \ C, C] = 0`, and
`det B = det B[C] det B[V \ C]`. Both factors are proper principal minors. For `-Q` they are
`det A_C > 0` and `det A_{V \ C} > 0`, because a proper killed block of an irreducible generator is a
nonsingular M-matrix (`lambda_C(0) > 0` by (P2)). So `det B > 0`, while `det B = det(-Q) = 0`. ∎

This is shorter than the route through Al Ahmadieh's Lemma 5.1 and Corollary 5.6, and it uses only the
positivity of the proper minors of `-Q`. For the generator case alone there is an even more direct
reading. A reducible generator has a closed class `C != V`, its killed block has zero row sums, so
`det(-Q'_C) = 0`, while `det A_C > 0`.

Check against `07_T4_literature.md`. Section (iii) there proves Lemma 3.1 and Proposition 3.3 in the
same way, and section (ii) step 3 is Lemma 3.2. Section (i) proves that a canonical cut-transpose of an
irreducible Z-matrix is always strongly connected, by algebra and by a direct path argument. So the
case that item (ii) of Target 3 anticipates, a cut-transpose whose pattern is not strongly connected,
does not occur for the canonical choice. Lemma 3.4 says more. No matrix of any sign pattern in the
fiber is reducible. The non-canonical factor choice with `alpha beta < 0` gives a matrix that is not a
Z-matrix (it differs by `diag(-I_X, I_Y)`), and it is excluded from the generators by Lemma 3.2, not by
reducibility. Target 3 item (ii) should be rewritten accordingly. The literature file and this note
agree on every statement.

## 4. Item 4d. Kim and Landim, and the case `d = 3`

### 4.1 What Kim and Landim prove in Section 5

Kim and Landim, "Gamma-expansion of the measure-current large deviations rate functional of
non-reversible finite-state Markov chains", arXiv:2412.13515 (v2), Section 5. The setting is a
continuous-time chain on a finite set `V` with jump rates `R(x,y)` and holding rates `lambda(x)`. The
functional is the Donsker and Varadhan rate `I(mu) = sup_{u > 0} -sum_x mu(x) (L u)(x)/u(x)`. The
statements below are paraphrased from the arXiv HTML text.

- Lemma 5.1. `I` determines the holding rates, `lambda(z) = I(delta_z)`, and the products
  `R(x,y) R(y,x)` for `x != y`. The proof restricts `I` to `theta delta_x + (1 - theta) delta_y`, where
  the two-state chain is reversible and the cross term is `-2 sqrt(R(x,y) R(y,x)) sqrt(theta(1-theta))`.
  No irreducibility is assumed.
- Lemma 5.2. With closed irreducible classes `V_1, ..., V_n`, `I` determines the invariant law of
  each class, through the zero set of `I` (their earlier Lemma A.8).
- Corollary 5.3. A reversible generator is determined by `I`, through Lemmas 5.1 and 5.2 and detailed
  balance.
- Example 5.4. The uniform 3-cycle `R(a,b) = R(b,c) = R(c,a) = 1` has
  `I(mu) = 1 - 3 (mu_a mu_b mu_c)^{1/3}`, and the reversed cycle has the same `I`. So `I` does not
  determine a non-reversible chain. They do not call the reversed cycle the time reversal.
- Lemmas 5.5 to 5.7 and Corollary 5.8 concern the measure-current functional of Bertini, Faggionato
  and Gabrielli. With all states recurrent it determines the rates (Corollary 5.8). Lemma 5.7 is the
  formula for the optimal flow that `rem:flows` of the draft already cites.

What they do not prove. They give no statement about principal minors of order three or more, no
description of the set of generators sharing `I`, no non-reversible identification up to time
reversal (not even for `d = 3`), and no use of killed faces or fields. The paper should cite Lemma 5.1
for `q_i` and `w_ij`, Corollary 5.3 for the reversible case, and Example 5.4 as the first instance of
the ambiguity, and present the `d = 3` corollary below as ours, derived from their Lemma 5.1.

### 4.2 The corollary

**Corollary 4.2.** Let `Q` and `Q'` be irreducible generators on three states with the same Donsker
and Varadhan functional. Then `Q' = Q` or `Q' = Q*`. Conversely `Q*` has the same functional as `Q`.

*Proof.* By Lemma 5.1 of Kim and Landim, `Q` and `Q'` have the same `q_i` and the same `w_ij`. These
are the principal minors of orders 1 and 2 of `-Q`. Expanding `det(-Q) = 0` gives

    c + c' = q_1 q_2 q_3 - q_1 w_23 - q_2 w_13 - q_3 w_12 =: sigma_3,    c c' = w_12 w_23 w_13 =: p_3,

with `c = q_12 q_23 q_31` and `c' = q_13 q_32 q_21` the two oriented 3-cycle products. The same holds
for `Q'`. So `{c, c'}` is the root set of `x^2 - sigma_3 x + p_3` for both chains. Either `Q'` has the
ordered pair `(c, c')` of `Q`, or it has the swapped pair `(c', c)`.

The pattern is determined by `(w, c, c')`. If `w_ij > 0` both arcs are present. If `w_ij = 0`, at most
one arc joins `i` and `j`, and it is present exactly when it lies on an oriented 3-cycle with positive
product. Indeed if, say, `q_12 > 0 = q_21`, irreducibility on three states forces a return path
`2 -> 3 -> 1`, so `c > 0`. And if `c > 0` then `q_12 > 0`. So `Q` and `Q'` with the same ordered pair
have the same pattern and the same product on every directed cycle (the 2-cycles carry `w_ij`, the
3-cycles `c` and `c'`).

Now `phi(i,j) = log(q'_ij / q_ij)` on the arcs has zero sum on every directed cycle. In a strongly
connected digraph such a function is a potential difference. Fix a root `o`, and let `p_j` be the sum
of `phi` along a directed walk from `o` to `j`. Two walks `P_1`, `P_2` to `j` give the same value,
because a walk `R` from `j` back to `o` closes both into closed directed walks, these split into
directed cycles, and so `phi(P_1) + phi(R) = 0 = phi(P_2) + phi(R)`. Then `phi(i,j) = p_j - p_i`, that
is `Q' = E^{-1} Q E` with `E = diag(e^{p})` positive. The diagonals agree and both are generators, so
Proposition 3.3 gives `Q' = Q`. In the swapped case the same argument compares `Q'` with `Q*`, whose
3-cycle products are `c* = q*_12 q*_23 q*_31 = q_21 q_32 q_13 = c'` and `c'* = c`, whose 2-cycle
products are `w_ij` and whose diagonal is that of `Q`. So `Q' = Q*`.

For the converse, `Q* + diag v = D^{-1}(Q + diag v)^T D`, so the Perron roots agree for all `v`, and
the functional, which is the Legendre transform of the Perron root of `Q + diag v`, agrees. ∎

On three states `Q* = Q` exactly when `c = c'` (Kolmogorov's criterion has only one cycle to check).
So the fiber of the functional has one point if `c = c'` and two points otherwise. Their Example 5.4 is
the case `c = 1`, `c' = 0`, `w = 0`.

### 4.3 Checks against the amplitude computation

From `06_amplitudes_output.txt`.

- Uniform 3-cycle. `Q* = Q^T`, and the principal minors agree exactly. The Kim and Landim functional
  satisfies `min_m [I(m) - v.m] = lambda_V(v)` to ten digits at two fields, which checks our
  normalization against theirs. At `v = 0` with uniform `mu`, `K_V = 0.8269933431 = 3 sqrt 3/(2 pi)`,
  which is Proposition 4.9(d) and `prop:threecycle` at `b = 1`. The pairs are reducible, so only `V`
  carries a Gaussian amplitude. With `mu` uniform (which is `pi`) the amplitudes of `Q` and `Q*` agree
  at every field, as Proposition 2.2 forces. With `mu = (0.5, 0.3, 0.2)` they agree at `v = 0`
  (Corollary 2.5 item 4) and differ at `v = (1,0,0)` by `-2.85e-2`, at `(0.3,-0.2,0.5)` by `-6.11e-2`
  and at `(0,1,0)` by `+8.54e-2`. So on the example of Kim and Landim the second-order amplitude
  breaks the reversal as soon as the start is not uniform and the field is not zero.
- A non-reversible 3-state chain with all `w_ij > 0`. The identities `c + c' = sigma_3` and
  `c c' = p_3` hold to ten digits (`3.66` and `0.216`), and the 3-cycle product of `Q*` along
  `1 -> 2 -> 3 -> 1` equals `c' = 0.06`. With `mu = pi` all amplitudes of `Q` and `Q*` agree on all
  faces. With `mu = (0.5, 0.3, 0.2)` every pair separates them at `v = 0` already (differences
  `0.27`, `0.084`, `-0.33`), and `V` separates them at `v = (1, 0, -0.5)` by `1.07e-2`. On a pair
  `{i,j}` the amplitudes agree for all fields exactly when `q*_ij = q_ij` or
  `mu_i q*_ij = mu_j q_ji`, which follows from `r = (1, rho)` with
  `rho^2 = (alpha_j/alpha_i)(q_ji/q_ij)` on a two-state face. At `mu = pi` the second alternative
  always holds, which is the pair form of Proposition 2.2.

## 5. Summary for the paper

- Exposure. State the descent version (Theorem 1.4 and Corollary 1.5) as the exposure lemma, with
  the non-reversible suppression Lemma 1.1. Use the singleton reference only for pairs and for faces
  whose irreducible proper subsets are singletons (Corollary 1.7), or state the general singleton
  version as a remark supported by numerics.
- Amplitudes. Replace "a non-stationary start separates the members of the fiber" by Theorem 2.8
  (generic start), with Proposition 2.2 (the stationary start cannot separate `Q` from `Q*`, exactly)
  and Corollary 2.5 (faces inside one side of a cut never separate the cut-transpose from `Q` or from
  `Q*`). The observability of `K_F` depends on the controlled crossing equation of Target 1 (i).
- Normalization and reducible points. Proposition 3.3 and Lemma 3.4 are complete and elementary.
- Kim and Landim. Cite Lemma 5.1, Corollary 5.3 and Example 5.4 as in Section 4.1, and present
  Corollary 4.2 as the `d = 3` case of Theorem 4.

Status. 4a proved in the descent form (every irreducible face, including `V`, is traced through a
boundary with a proper subface, by induction from the singletons), and proved with the singleton
reference for pairs and for faces without irreducible proper subsets of size at least 2. The general
singleton-reference version is inconclusive, with the first unresolved implication (Open) of
Section 1.5. 4b computed and proved (Lemma 2.1, Proposition 2.2, Lemma 2.4, Corollary 2.5,
Proposition 2.6, Theorem 2.8), with an obstruction found for the claim as stated (stationary start
never separates `Q` from `Q*`, and faces inside one side of a cut never separate a cut-transpose).
Its translation to observed boundaries is proved under the hypothesis that the controlled crossing
equation of Target 1 (i) holds. 4c proved. 4d proved.
