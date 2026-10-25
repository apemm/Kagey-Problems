# 27. Audit of (O4) and of the exact Bessel range in Paper C1 (October 25, 2026)

Scope: the results added in note 25. Labels as in the source (numbers as in the current build):
`thm:crossing` (Theorem 5.8, part (iv)), `lem:derivative` (Lemma A.5), `prop:layer-cubic`
(Proposition 6.2), `prop:layer-constants` (Proposition 6.6, part (v)), and how `thm:layer`(c)
uses them. Method: claim card, my own derivation of the critical step before reading the proof,
then each implication checked, then numerical spot checks (exact sums or 40 to 50 digit
arithmetic, scripts in a scratch folder, not in the repo).

Verdicts:

| Result | Verdict |
|---|---|
| Lemma A.5 (`lem:derivative`) | proved as written |
| Theorem 5.8(iv) | proved as written |
| Proposition 6.6(v) | proved as written |
| Proposition 6.2(a)-(e) | proved as written |
| `thm:layer`(c) uses only affinity | confirmed |

No gap found. Optional polish is listed at the end.

---

## 1. Lemma A.5 and Theorem 5.8(iv)

### Claim card

- **Lemma A.5.** F satisfies (H), k >= 2, K a compact subset of the open face. There are T_1, N_0
  and C such that for N >= N_0, supp n = F, n/N in K and T_1 <= T <= N^(1/3),
  |d/dT log P_N(n) + J_F(n/N)| <= C/T. The derivative is taken at fixed N and n, so P_N(n) is a
  polynomial in T.
- **Theorem 5.8(iv).** If F and G satisfy (H), Delta = k_F - k_G >= 1 and delta = lambda_G -
  lambda_F > 0, then for large N, D_N = log M_F - log M_G has exactly one zero in [1, N^(1/3)].

### My derivation before reading

With h = T/N, T d/dT = h d/dh. The m-th term of the run expansion has logarithmic h-derivative
(M-1) - sum_i (n_i - m_i) hq_i/(1-hq_i). So T d/dT log P_N(n) is the mean of this under the law
w~ on m proportional to the terms. The second part is T<q,alpha> + O(T^2/N) once E M = O(T). For
E(M-1), tilt A_F to e^c A_F. Then E(M-1) = Upsilon'(0) with Upsilon(c) = log P^(c) - log P^(0),
which is convex. The continuum sum for e^c A_F is H_{e^c}(t) = e^{c(k-1)} H(e^c t), because a
word has M-1 switches and the monomial has degree M-k. The local law at time e^c T then gives
Upsilon(c) = (k-1)c/2 + (e^c - 1) T<theta,alpha> + O(1/T). The O(1/T) has no derivative bound,
but convexity gives Upsilon'(0) between the difference quotients at step eta. With eta = 1/T the
curvature error is O(T eta) and the remainder error is O(1/(T eta)). Both are O(1). So
E(M-1) = T<theta,alpha> + O(1), and T d/dT log P = -T J_F + O(1).

For the theorem: log M_F is a maximum of finitely many smooth functions log P_N(n), so it has
one-sided derivatives at every T: the largest and the smallest d/dT log P_N(n) over the
maximizers at T. If every maximizer is near alpha*_F, the lemma makes both equal to
-lambda_F + O(1/L).

### Implications checked

1. *The log-derivative identity.* Correct. Terms with m_i > n_i vanish identically in h. Every
   other term is positive for 0 < h < 1/q_max, so the logarithm is defined.
2. *Lemma 5.5 for the weights e^c A_F with the old diagonal q.* P^(c) is not a probability, and
   q is no longer the row sums of e^c A_F. The proof of Lemma 5.5 uses neither fact. Step 1 is the
   algebraic identity sum_m v_m = h^{k-1} e^{-<q,t>} H(t), which holds for any q. Step 2 (the
   bounds on kappa_m) uses only hq_max <= 1/2 and n_min. Steps 3 and 4 use only
   Upsilon(1) <= C T. For base weights e^c A_F,
   Upsilon(1) = log H_{e^{c+1}}(t) - log H_{e^c}(t). The upper bound is (A-Hsigma) with
   sigma = e^{c+1} <= e^2, which holds for every sigma > 0. The lower bound is the local law at
   time e^c T >= 1, which needs T >= e (so T_1 = e works). Uniform in |c| <= 1. Correct.
3. *The identity H_{e^c}(t) = e^{c(k-1)} H(e^c t).* Checked from the definition of H. Correct.
4. *The form of Upsilon.* The local law at time e^c T with alpha fixed gives
   H(e^c T alpha) = (e^c T)^{-(k-1)/2} C_F(alpha) e^{e^c T<theta,alpha>}(1+O(1/T)), with an
   O(e/T) error uniform on K. Substituting gives a(c) as stated. The error is O(1/T + T^2/N),
   and T^2/N <= 1/T for T <= N^(1/3). Correct, with eps(0) = 0 exactly.
5. *Convexity step.* a'' = e^c T<theta,alpha> <= C_2 T on [-1,1], and eta = 1/T <= 1. The bound
   2C_1/(T eta) is conservative: C_1/(T eta) suffices since eps(0) = 0. Correct.
6. *The other term.* sum_i hq_i n_i/(1-hq_i) = T<q,alpha>(1+O(h)), with Th = T^2/N, and the
   m-part is O(h E M) = O(T^2/N). Correct.
7. *The window.* The proof of (ii) gives T_N > Delta L/(2 delta) strictly and
   T_N <= Delta L/delta + O(1) for every zero in [1, N^(1/3)]. So every zero lies in
   W = [Delta L/(2 delta), 2 Delta L/delta], and W is inside [1, N^(1/3)] for large N. Correct.
8. *From pointwise derivatives to the lattice maximum.* For a finite maximum of C^1 functions,
   the right derivative is the largest derivative among the active indices and the left
   derivative is the smallest. The polynomials are positive on W. Correct.
9. *Uniformity at the maximizers.* Theorem 5.7 with v = 0 puts every maximizer at
   alpha*_F + O(1/T), uniformly on [1, N^(1/3)]. On W this is O(1/L), so the maximizers lie in a
   fixed closed ball K around alpha*_F, where Lemma A.5 applies with one constant. Then
   J_F(n/N) = lambda_F + O(1/L). In fact it is O(1/L^2), since alpha*_F minimizes J_F. Correct.
10. *G a singleton.* d/dT [(N-1) log(1 - T q_j/N)] = -q_j + O(L/N) on W, and lambda_{j} = q_j.
    F cannot be a singleton, since Delta >= 1. Correct.
11. *D_N' > 0 on all of W.* D^+ D_N = D^+ log M_F - D^+ log M_G = delta + O(1/L) >= delta/2.
    A continuous function with positive right derivative at every point of an interval is
    strictly increasing there. With (i), exactly one zero. Correct.

### Spot checks

- *Lemma A.5, exact.* A 3-state chain, F = {1,2}, q_12 = 1, q_21 = 2, leaks q_13 = 0.5 and
  q_23 = 0.3, mu = (1/2, 1/2, 0), N = 10^7. The exact run expansion was summed in log domain, and
  the exact mean was taken for T d/dT log P_N(n). For alpha_1 = 0.3, 0.5 and 0.7 and T = 10, 20,
  40 and 80, the difference T d/dT log P_N(n) + T J_F(alpha) was 0.510, 0.505, 0.502 and 0.500
  (alpha_1 = 0.3), and similarly for the other two values of alpha_1. It tends to (k-1)/2 = 1/2,
  the derivative of the power T^{(k-1)/2}, at rate O(1/T). So the remainder is O(1), as the
  lemma says.
- *Theorem 5.8(iv).* The same chain with N = 10^6, F = {1,2} against G = {1}
  (delta = 1.0695), on a grid of step 0.5 over [1, 100]. M_F was found by an integer ternary
  search in n_1, which assumes unimodality in n_1, so this is a spot check only. D_N was
  strictly increasing on the whole grid, with least difference quotient 1.075 and a single sign
  change, in (11.0, 11.5).

---

## 2. Proposition 6.6(v) and Proposition 6.2

### Claim cards

- **6.6(v).** z -> J_G(beta, z) is affine on [0, infinity) if and only if
  pi_in_beta = pi_out_beta. Then J_G(beta, z) = J_G(beta) - z omega_beta, and
  Jbar_F(S beta, x) = S J_G(beta) + q_i x - 2 sqrt(omega_beta S x) for all x > 0.
- **6.2(a).** r_beta is real-analytic at 0, r_beta(eps) = kappa_beta eps^3 + O(eps^4), and
  kappa_beta = J'''/(6 omega^{3/2}) + (gamma - q_i)^2/omega^{1/2}.
- **6.2(b).** |log(f_F/(f_G B_beta)) + S r_beta(sqrt(x/S))| <= C(1/T + sqrt(x/T)) for
  0 < x <= delta T.
- **6.2(c).** If the laws agree, then r_beta = 0.
- **6.2(d).** If the first nonzero Taylor coefficient of r_beta has order m >= 3, the ratio tends
  to 1 if and only if x/T^{1-2/m} -> 0 (for x <= delta_beta T). If r_beta = 0, the ratio tends
  to 1 whenever x/T -> 0.
- **6.2(e).** For the 3-cycle (2,2,2 forward, 1,1,1 back), i = 3 and beta = (1/2, 1/2):
  omega = 2 + (9/4) sqrt 2, J''' = -(1323/64) sqrt 2, kappa = -49/(64 sqrt omega), so m = 3.

### My derivation before reading

*Affinity.* J_G(beta, z) = sup_psi [Psi_beta(e^psi) - z P_beta(e^psi)], a concave problem in psi.
At psi_0 = log r_beta the gradient of Psi vanishes, and the gradient of P is
omega(pi_out - pi_in). If the laws agree, psi_0 is critical, hence maximal, for every z >= 0,
and J is affine with slope -P(r_beta) = -omega. Conversely, the implicit function theorem gives
d^2J/dz^2 at 0 = gradP^T L^+ gradP, where L is the Laplacian of the conductances kappa, which is
positive semidefinite with kernel the constants. Since gradP sums to zero, the second derivative
vanishes only when gradP = 0.

*The cubic.* j(eps) = sup_z [J_G(beta, z) - eps^2/z]. Put z = eps w and expand J_G to third
order: (j - J_G)/eps = max_w [-omega w - 1/w + a eps w^2 + c eps^2 w^3] + O(eps^3), with
a = J''/2 and c = J'''/6. At w_0 = omega^{-1/2} we have phi'' = -2 omega^{3/2}. The maximum is
phi(w_0) + p(w_0) + p'(w_0)^2/(4 omega^{3/2}) + O(eps^3), so
j_3 = c omega^{-3/2} + a^2 omega^{-5/2}. With a = omega(gamma - q_i) this is kappa_beta.

*The iff.* With X = S eps^m, of order (x/T^{1-2/m})^{m/2}, the log ratio is -rho_m X(1 + o(1))
+ O(1/T + sqrt(x/T)). The only question is whether sqrt(x/T) can mask X. If X >= eta, then
u = x/S >= (eta/S)^{2/m}, and sqrt(u)/X = u^{-(m-1)/2}/S <= eta^{-(m-1)/m} S^{-1/m} -> 0. So it
cannot.

### Implications checked

1. *6.6(v), forward.* The gradient of P at psi_0 is c+_m r_m a - b c-_m l_m =
   omega(pi_out_m - pi_in_m). Concavity in psi makes the critical point a maximizer for each
   z >= 0, on all of [0, infinity), not only near 0. Jbar_F then follows from (i), and the
   exchange of two suprema in (i) is always valid. Correct.
2. *6.6(v), converse.* Affine on [0, infinity) implies J'' = 0 at 0, since J is real-analytic
   near 0. Then gradP^T L^+ gradP = omega^2 (pi_out - pi_in)^T L^+ (pi_out - pi_in) =
   2 omega (gamma - q_i) = 0, and gradP is orthogonal to the constants, so pi_out = pi_in.
   Correct. The Hessian of Psi at psi_0 is -L with conductances
   kappa_{jj'} = l_j q_{jj'} r_{j'} + l_{j'} q_{j'j} r_j (checked term by term).
3. *6.2(a).* The implicit function theorem applies to grad Psi = eps grad P/sqrt(P), which is
   analytic since P > 0. z(eps) = eps/sqrt(P(psi(eps))) is a maximizer of
   J_G(beta, z) - eps^2/z, because J_G(beta, z(eps)) >= Psi - z(eps) P at psi(eps), and that
   value is j, the supremum. z(eps) is about eps/sqrt(omega), inside the disc where the
   holomorphic J_G equals the rate. The O(eps^3) remainders are as claimed. Correct.
4. *6.2(b), x <= 1.* `thm:layer`(b) together with S|r_beta| <= C x^{3/2} S^{-1/2} <=
   C sqrt(x/S). Correct.
5. *6.2(b), 1 <= x <= delta T.* On I = [z*/2, 2z*] we have
   2x/z^3 >= x/(4 z*^3) = omega S/(4 z*), which beats |R''| <= C(1+S) once z* is small. So
   lambda is convex on I, the critical point rho_s lies in I, and lambda(rho_s) = min_I lambda.
   Further |lambda - lambda_0| = |g| = O(z*) on I, and min_I lambda_0 is the global extremum
   because z(eps) lies in I. The error terms O(sqrt(x/S) + 1/zeta) from the proof of (b) are
   consistent: 1/S <= C/zeta, and x/zeta = O(sqrt(x/S)). Correct.
6. *6.2(c).* 6.6(v) gives r_beta identically 0, for every eps and not only near 0. Correct.
7. *6.2(d).* The "if" direction: X -> 0 forces u^{m/2} <= X/S -> 0, so x/T -> 0 and both terms
   vanish. The "only if" direction is the masking computation above, and it matches the
   paper's. S is in [T/2, T], and eps <= sqrt(2 delta_beta) holds since x/S <= 2 delta_beta.
   The sentence for r_beta = 0 is one-way and is stated one-way. It is not an iff: at x of
   order T, `thm:layer`(c) gives a ratio of 1 + c_1 z* I_0/I_1 + O(x/T), which does not tend to
   1 unless c_1(beta) = 0. The paper does not claim an iff here. Correct.
8. *6.2(e).* For (e) the sign is needed, not only |ell|. It holds because
   r_beta <= kappa eps^3/2 < 0 for small eps, so -S r_beta >= |kappa| X/2. Correct.
9. *`thm:layer`(c) uses only affinity.* Its proof cites 6.6(v) for J_G(beta, z) =
   J_G(beta) - z omega on [0, 2z_0), extends this to the disc by the identity theorem, and then
   uses Xi = C_G(beta, z)/C_G(beta, 0), which also needs gamma = q_i. That follows from affinity
   by 6.6(ii). Nothing else about the two laws is used. Confirmed.
10. *The 4-state example after 6.2.* At uniform beta, r_beta is proportional to ones exactly
    when the row and column sums of A_G agree (both are 3), so pi_in = pi_out. I also checked
    "at other beta the two laws differ". The laws agree if and only if u = sqrt(beta) is
    critical, which here reads sum_j sqrt(beta_j)(q_{jj'} - q_{j'j}) = 0 for each j'. For the
    cycle this gives sqrt(beta_3) = sqrt(beta_2) and its rotations, so beta is uniform. Correct.

### Spot checks

- *Affinity, non-reversible facet with pi_in = pi_out.* G is the 3-cycle above, and i is a
  fourth state with q_{ji} = q_{ij} = c = 0.7. I computed J_G(beta, z) by direct optimization
  over u at 40 digits, for z = 0, 0.5, 1 and 2. At uniform beta the defect from the chord was
  0 to 40 digits, and J(z) = c - 3zc^2 (so omega = 3c^2), as predicted. At beta = (0.5, 0.3, 0.2)
  the defects were -9.4e-5 at z = 0.5 and +5.3e-4 at z = 2, so J is strictly convex and not
  affine.
- *The 3-cycle constants.* From J_G(beta, z) = 3 - 2z - sqrt((2+z)(1+4z)), exact derivatives
  computed symbolically: -2 - (9/4) sqrt 2, (49/16) sqrt 2 and -(1323/64) sqrt 2. Then
  kappa sqrt(omega) = -49/64 exactly, and kappa = -0.336332021976940.
- *An independent route for kappa.* I computed r_beta(eps) from the full 3-state rate J_F (a
  two-dimensional optimization, without using 6.6(i)). The values of r_beta(eps)/eps^3 at
  eps = 0.02, 0.01 and 0.005 are -0.33100, -0.33365 and -0.33498. They are linear in eps, and
  the limit is -0.3363.
- *The range, from exact densities.* For the 3-cycle with mu = (1/2, 1/2, 0) and T = 4000, I
  computed f_F exactly by the contour formula `eq:layer-contour` with the closed form of
  f_G^(z) from `lem:L-two`. This used a trapezoid rule on |z| = z* with 6000 nodes at 50 digits.
  I compared log(f_F/(f_G B_beta)) with -S r_beta(sqrt(x/S)):

  | x | log ratio | -S r_beta | difference | sqrt(x/T) |
  |---|---|---|---|---|
  | 1 | 0.0219 | 0.0053 | 0.0167 | 0.0158 |
  | 10 | 0.2140 | 0.1618 | 0.0522 | 0.0500 |
  | 50 | 1.849 | 1.734 | 0.115 | 0.112 |
  | 100 | 4.929 | 4.768 | 0.161 | 0.158 |
  | 200 | 13.24 | 13.01 | 0.226 | 0.224 |
  | 400 | 35.61 | 35.29 | 0.318 | 0.316 |

  The difference tracks sqrt(x/T) with coefficient about 1. So the bound in 6.2(b) holds and is
  attained in order. The log ratio itself grows like |kappa| x^{3/2} T^{-1/2}. It is already
  about 13 at x = 200, about 12.6 T^{1/3}, so the relative Bessel form fails beyond T^{1/3}, as
  (d) and (e) say.

---

## Optional polish (no correctness impact)

- `lem:derivative`: T_1 = e can be named, since Step 1 needs only T >= e. In Step 2,
  2C_1/(T eta) can be C_1/(T eta), since eps(0) = 0.
- `lem:derivative`, Step 1: one clause would help the reader, saying that Lemma 5.5 never uses
  that q is the row sums of the weights, or that P^(c) is a probability.
- `thm:crossing`(iv): J_F(n/N) = lambda_F + O(1/L^2) holds, since alpha*_F minimizes J_F. O(1/L)
  is enough.
- `prop:layer-cubic`(d): the sentence for r_beta = 0 is one-way. A reader might expect an iff by
  analogy, and at x of order T the ratio is 1 + c_1 z* I_0/I_1 + O(x/T). A half-sentence could
  say so, but this is not required.
