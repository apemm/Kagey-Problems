# Paper F audit 01: the bulk theorem, inputs and Steps 1 to 4

Scope: `paperF/sec_setting.tex` (definitions, hypotheses, kernels, fresh-plus
identity) and `paperF/sec_bulk.tex` up to and including Step 4 (line 520).
Steps 5 and 6 were read only where Steps 1 to 4 rely on them. No file was edited.

Source used for Caravenna and Doney: arXiv:1612.07635v3, text saved at
`research_notes/Occupation novelty and compact advances/evidence_02/CaravennaDoney2016v3.txt`
(Theorem 1.1 on PDF page 2; Section 2.3 and (2.5)-(2.7) on PDF page 10).

Line numbers refer to `sec_bulk.tex` unless stated.

---

## 1. Lemma lem:stable (lines 48-137)

### (i) Domain of attraction and normalization: verified

- The identity `e^{-sx}-1+sx = int_0^x s(1-e^{-sy}) dy` is right (differentiate
  in x). Fubini is justified because `|s(1-e^{-sy})| <= |s| min(2,|s|y)` and
  `\bar T` is integrable.
- The substitution `y = v/lambda` gives the displayed second form exactly.
  `|1-e^{-w}| <= min(2,|w|)` for `Re w >= 0` gives the stated domination.
- The dominating function `min(2,v) * 2max(v^{-a-d}, v^{-a+d})` is integrable at
  0 (needs `a+d<2`) and at infinity (needs `a-d>1`); both hold by the choice of d.
  The near-zero piece is `O(lambda^2)/\bar T(1/lambda) -> 0` because `\bar T(1/lambda)`
  is RV of index `alpha<2` in lambda. Uniformity in phi holds because the
  dominating function and the pointwise error `|ratio - v^{-alpha}|` do not
  depend on phi.
- `F(1) = Gamma(2-a)/(a-1) = -Gamma(1-a) = K_a`: checked by integration by parts
  and `Gamma(2-a) = (1-a)Gamma(1-a)`. The identity theorem gives `F(s)=K_a s^a`
  on `Re s>0`, and continuity extends it to the boundary.
- `E e^{-s(X-mu)} - 1 = Phi(s) + O(|s|^2)`: checked
  (`e^{s mu}(1 - s mu) - 1 = O(|s|^2)`, and `(e^{s mu}-1)Phi(s) = o(Phi(s))`).
  With `s = -i theta/a(m)`, `m \bar T(a(m)/|theta|) -> |theta|^alpha` and
  `m/a(m)^2 -> 0` (because `2/alpha > 1`), the limit is `K_a(-i theta)^a`. With
  `s = 1/a(m)` the limit is `K_a`, which is the last claim. Jensen gives
  `E e^{-(X-mu)/a} >= 1`, consistent with `K_a > 0`.

### (ii) Gnedenko local limit and the bound u-bar: verified (one cosmetic point)

- (SPAN) says the integer support has gcd of differences 1, so the lattice span
  of `X - mu` is 1. Ibragimov-Linnik Thm 4.2.1 is stated with arbitrary centering
  and scaling constants, so it applies directly with `A_n = n mu`, `B_n = a(n)`.
- The cited Caravenna-Doney form is accurately described: (2.5) takes
  `J=(-v,0]` with v the lattice span, and (2.6) reads
  `lim_n sup_x |a_n P(S_n in x+J) - v phi(x/a_n)| = 0`. With `v=1` and `x=k-m mu`
  the event is `{S_m = k}`. **Cosmetic:** CD's `a_n` is `A^{-1}(n)`, not the
  paper's `a(n)`. Passing from one to the other needs `a_n/a(n) -> 1`, plus
  boundedness, uniform continuity and decay of g to control
  `g(x/a_n) - g(x/a(n))` uniformly in x. That takes one line, and the
  Ibragimov-Linnik citation makes it unnecessary.
- u-bar: `a(m)P <= ||g||+1` for `m >= m_0`, and `a(m)P <= a(m) <= a(m_0)` for
  `m < m_0`. Correct, provided `a > 0` (see gap C3).

### (iii) Local large deviations: verified against the source

Line by line against arXiv v3:
- CD hypothesis (1.2): `\bar F(x) = P(X>x) ~ p/A(x)` and `F(-x) = P(X <= -x) ~ q/A(x)`,
  with `A in RV(alpha)`. "We assume that p>0 and q>=0 (when q=0, the second
  relation in (1.2) should be understood as F(-x)=o(1/A(x)))". For alpha>1 they
  also assume `E X = 0`. For `X - mu` the left tail is identically 0 beyond
  `mu-1`, so q=0 is allowed, and `p=1` with `A(x) := 1/P(X-mu>x)`, which is
  RV(alpha). WLOG (CD Section 2.2) A is replaced by a smooth, strictly increasing,
  asymptotically equivalent version. This changes only constants.
- **Role of q = 0.** CD require only p>0. The q=0 case is explicitly covered,
  and the positivity parameter `rho = 1 - 1/alpha` lies in (0,1/2), so it is
  positive. Nothing in (1.6) needs a two-sided tail. The vanishing left tail is
  used again, separately, in (iv), where it supplies the exponential moment of
  `-(X-mu)`.
- CD (1.6): "for some `C'_0 = C'_0(J) < infinity`,
  `P(S_n in x+J) <= C'_0 (1/a_n)(n/A(x))`", stated for all `n in N` and `x >= 0`
  under the hypotheses of Thm 1.1, with J bounded and measurable. The paper's
  transcription `C'_0(J) m/(a_m A(x))` is exact. `J=(-1,0]` and `x = j - m mu >= 1`
  are admissible.
- The direction of the constants is right: the paper needs `1/a_m <= c/a(m)`,
  that is `a(m) <= c a_m`, which is what it states. It also needs
  `1/A(x) <= c T(x)` on `x >= 1`. This holds because
  `1/A(x) ~ P(X > x+mu) <= T(x)` and T is bounded below on compacts (the support
  is infinite).
- (1.6) needs no aperiodicity. Its proof uses (2.7), which holds for any law.
  Relevant to gap C2.
- **Cosmetic:** "Potter's bounds for A give `a_m/a(m) -> 1`". The correct tool is
  that asymptotic inverses of asymptotically equivalent RV functions with
  positive index are asymptotically equivalent (BGT Thm 1.5.12), not Potter.
- The remark "(1.6) has no factor 1/x" is correct, and so is the warning that
  `m T(x)/x` would need (LR).

### (iv) Chernoff left deviation: verified line by line

1. `C_- = sup_m m log E e^{-(X-mu)/a(m)}`. Each term is finite because
   `X >= 1` gives `E e^{-(X-mu)/a(m)} <= e^{(mu-1)/a(m)}`. By (i),
   `m(E e^{-(X-mu)/a(m)} - 1) -> K_a`, so it is bounded. With
   `log(1+z) <= z` (valid for z > -1, and here z >= 0 by Jensen), `C_-` is finite.
   Also `C_- >= 0` by Jensen, so `e^{C_-} >= 1` and the bound is never vacuous in
   the wrong direction.
2. `P(S_m - m mu <= -y) = P(e^{-(S_m-m mu)/a(m)} >= e^{y/a(m)}) <= e^{-y/a(m)} E e^{-(S_m - m mu)/a(m)}`
   (Markov's inequality).
3. Independence and identical distribution of the m summands give
   `E e^{-(S_m-m mu)/a(m)} = (E e^{-(X-mu)/a(m)})^m = exp(m log E ...) <= e^{C_-}`.
4. The bound holds for all `m >= 1` and all real y (y >= 0 is not even needed).

**Cosmetic:** "It uses only that `X_sigma` is bounded below" is slightly
overstated. The finiteness of `C_-` also uses (i), that is (RV). The Fuk-Nagaev
attribution is decorative.

---

## 2. Kernel facts (K1)-(K4) and Lemma lem:kernels (lines 145-194)

- (K1): `sum_m u_m(j) = u(j) <= 1` (it is a probability), `sum_m q_m(j) = 1`, and
  `sum_m q_{m+1}(j) = 1 - T(j) <= 1`, by (eq:kernel-sums), which is itself proved
  correctly in sec_setting (unique covering index). Verified.
- (K2): `u_m(j) = 0` for m>j since `S_m >= m`. `q_m(j)` needs `S_{m-1} < j`, so
  `m-1 < j`. `q_{m+1}(j)` needs `m < j`. Verified. For `j <= 0` all kernels vanish,
  which is consistent with the convolution formula because T is extended by 0.
- (K3): `{J=m} = {S_{m-1} < j <= S_m}`, and `{S_m = j} subset {J = m}` because the
  partial sums increase strictly. Verified.
- (K4): `sum_j P(S_{m-1} < j <= S_m) = E X_m = mu`. Verified.

**Bound `W_m(j) <= C_1/a(m)`: verified.** For u: `u-bar <= mu rho u-bar` because
`mu >= 1` and `rho >= 1` (a is increasing). For `q_m`, m>=2:
`<= mu u-bar/a(m-1) <= mu rho u-bar/a(m)`. For `q_1 = T <= 1 <= C_1/a(1)`. For
`q_{m+1}`: `<= mu u-bar/a(m)`. All correct.

**Local limits: verified, with the order of limits correct.**
- `a(m-1)q_m(j) - mu g(z) = sum_v T(v)[a(m-1)u_{m-1}(j-v) - g(z)]`, using
  `sum_v T(v) = mu`. Shifts `v > V` contribute at most `(u-bar + ||g||) sum_{v>V} T(v)`.
- For `v <= V` the argument is `z a(m)/a(m-1) + (mu - v)/a(m-1)`. This was
  checked: `j - v - (m-1)mu = (j - m mu) + (mu - v)`. For `|z| <= Z` it is within
  `eps_m` of z. For `|z| > Z`, both `g(z')` and `g(z)` lie in `[0, g-bar(Z/2)]`
  once `Z a(m)/a(m-1) - (V+mu)/a(m-1) >= Z/2`, so their difference is at most
  `g-bar(Z/2)`.
- Order: for fixed V and Z, letting m go to infinity kills `delta_u(m-1)` and
  `omega_g(eps_m)`. Then V and Z go to infinity. Replacing `a(m-1)` by `a(m)`
  costs `|a(m)/a(m-1) - 1| mu ||g|| + (a(m)/a(m-1) - 1)` times a bounded quantity,
  uniformly in j. All of this is uniform in `j in Z`.
- `q_{m+1}`: the argument is `z - v/a(m)`, which is simpler. Correct.

(The task description calls the truncation level "J". In the text it is V. See
the notation remark in C5.)

---

## 3. Lemma lem:small (lines 196-242)

**First claim: verified.**
- If `4m mu <= i`, then `i - m mu >= 3i/4 >= i/2 >= 2 >= 1` (since `m >= 1` and
  `mu > 1`), so (iii) applies. Also `T(i - m mu) <= T(i/2) <= C_T T(i)`, with
  `C_T = sup_{x>=1} T(x/2)/T(x)` finite by (RV) and positivity on compacts.
  `C_LD C_T <= C_2`.
- `q_m`, m>=2, split at `v = j/2`:
  - `v <= j/2`: `j - v >= j/2 >= 4m mu >= 4(m-1)mu`, so
    `u_{m-1}(j-v) <= C_LD C_T (m-1) T(j-v)/a(m-1) <= C_LD C_T^2 rho m T(j)/a(m)`.
    The weights sum to at most mu.
  - `v > j/2`: `T(v) <= C_T T(j)` and `sum u_{m-1} <= 1` by (K4).
- `q_{m+1}` is the same with `u_m` and `j - v >= 4m mu`. `q_1 = T <= C_2 T`.
- `C_2 = C_T + mu C_LD C_T^2 rho` dominates every case. Correct.

**Potter step: verified.** `y/a(y)` is RV with index `1 - 1/alpha > 0`, positive,
and bounded above and below on compacts of `[1, infinity)`. So
`sup_{1<=y<=x} y/a(y) <= C_P x/a(x)` for all `x >= 1`. The correct reference is
BGT Thm 1.5.3, or 1.5.6(iii) plus the compact extension. This applies with
`m <= eps N/(8 mu) <= N`. `T(j) <= T(eps N) <= C_{T,eps} T(N)`. Then
`(1 + C_P N/a(N)) <= (1 + C_P)(1 + N/a(N))`, so `C_3 = C_2(1+C_P)C_{T,eps}`
works. Constants depend on the law and eps only.

**Index computation: verified independently for every pair of indices.**

My derivation. Index of `B_N` (as a function of N): `B_N = max(a_+(N/s), a_-(N/s))`.
- If `alpha_+ != alpha_-`, the ratio of the two scales goes to 0 or infinity, so
  `B_N` is asymptotic to the scale with index `1/alpha_*`.
- If `alpha_+ = alpha_- = alpha`, `B_N = N^{1/alpha} max(l_1, l_2)`, and the max
  of two slowly varying functions is slowly varying (each `l_i(lambda x) = l_i(x)(1+o(1))`).
  So the index is `1/alpha = 1/alpha_*` even when the ratio oscillates.

Index of `e_{sigma,N} = (1 + N/a_sigma(N)) T_sigma(N)`: `N/a_sigma(N) -> infinity`,
so `e ~ N T_sigma(N)/a_sigma(N)`, with index `1 - 1/alpha_sigma - alpha_sigma`.

Sum: `I(sigma) = 1/alpha_* + 1 - 1/alpha_sigma - alpha_sigma`.
- sigma with `alpha_sigma = alpha_*` (the sign with the larger scale when the
  indices differ, and either sign when they are equal): `I = 1 - alpha_* < 0`.
- sigma with `alpha_sigma = alpha^* > alpha_*` (the sign with the smaller scale):
  `I = 1 - alpha^* + (alpha^* - alpha_*)/(alpha_* alpha^*)`. Since
  `alpha_* alpha^* > 1`, `I < 1 - alpha^* + alpha^* - alpha_* = 1 - alpha_*`.
  Extreme check: `alpha_* = 1.01`, `alpha^* = 1.99` gives
  `I = 0.990 - 0.503 + 1 - 1.99 = -0.503`.
- In all four combinations (`alpha_+ < alpha_-`, `alpha_+ > alpha_-`, equal; and
  sigma either sign) `I <= 1 - alpha_* < 0`. The paper's inequality
  `1/alpha_* - 1/alpha_sigma <= alpha_sigma - alpha_*` is exactly this. Also
  `B_N T_sigma(N)` has index `1/alpha_* - alpha_sigma <= 1/alpha_* - alpha_* < 0`.
  The paper's claim matches mine.

This is the step where the bound must hold for the sign with the smaller scale,
because Step 2 multiplies `e_{+,N}` by `B_N` whichever sign dominates. It does
hold.

---

## 4. Lemma lem:index (lines 244-318)

**(a), reduction: verified.** `sum_{m notin I} u_m <= sum_{m notin I} q_m = P(J notin I)`
by (K3). For `q_{m+1}`: `sum_{m notin I} P(J = m+1) <= P(J-1 notin I)`. Both
events are contained in `{J <= m_- + 1} union {J > m_+}`.

**Too few runs (right deviation): verified.** `m' = floor(m_-+1)`. Because J is
an integer, `J <= m_- + 1` iff `J <= m'`, which implies `S_{m'} >= S_J >= j`
(a deterministic implication). `j - m' mu >= K a(j/mu) - mu`. Once
`K a(j/mu) >= mu`, `m' <= j/mu`, so `a(m') <= a(j/mu)` and
`(K a(j/mu) - mu)/a(m') >= K - mu/a(j/mu) >= K - 1`. Then
`limsup P(Z_{m'} >= K-1) <= P(Z >= K-1)` by the portmanteau theorem (closed set),
since `m'(j) -> infinity`. Correct. This uses (i), not (iii).

**Too many runs (left deviation): verified, and no independence between the
count and the sum is assumed.** `m'' = floor(m_+)`. `J > m_+` iff `J >= m''+1`
iff `S_{m''} < j`, again a deterministic implication from the definition of J.
Then `S_{m''} - m'' mu < j - m'' mu <= -(K a(j/mu) - mu)`, because
`m'' > m_+ - 1`. So the event is contained in `{S_{m''} <= m'' mu - y}` with
`y = K a(j/mu) - mu`. This is a fixed-index negative deviation of a sum of i.i.d.
runs, and (iv) applies directly. Then `m'' <= 2j/mu`, and
`a(2j/mu)/a(j/mu) -> 2^{1/alpha} < 2`, give
`y/a(m'') >= K/2 - mu/(2a(j/mu)) >= K/2 - 1`. The bound `e^{C_- + 1 - K/2}` follows.
The only probabilistic input is the i.i.d. structure of one sign's runs. The
random index J is eliminated by the inclusion of events, not by conditioning.

**(b): verified.** For `m in I`, `m mu/j -> 1` uniformly, so `a(m)/a(j/mu) -> 1`
uniformly by the uniform convergence theorem. Lemma lem:kernels gives
`W_m(j) = (c_W g(y_m) + o(1))/a(j/mu)` uniformly. There are at most
`2K/Delta + 1` lattice points, so the o(1) terms total
`o(1)(2K/mu + 1/a(j/mu)) -> 0`. The Riemann-sum error bound
`2K(omega_g(Delta) + ||g|| omega(Delta)) + 2 Delta ||g||` is right and uniform
over `Psi(omega)`. The tails cost `eta(K) + (c_W/mu)P(|Z|>K)`. Then K goes to
infinity. Correct.

---

## 5. Steps 1 to 4 of the proof (lines 370-520)

**Choice of eps and constants (lines 384-392): verified.** eps depends only on
p, `mu_+` and `mu_-`. `C_4 = 1 + 8C_1/eps`, `c_0 = s/mu_min`, `c_1 = 2s/mu_min`,
`c_2 = 2/eps`, `kappa = s/(2 c_1 mu_max)` and `eta(K)` all depend on the laws
(and the fixed choice of `a_sigma`) only. None depends on N, k, or theta_N. K
and R enter only through thresholds `N_2(K)` and `N_3`, and through `K(R)`,
which is a law-dependent multiple of R.

**Step 1, decomposition (eq:bulk-pairs), (eq:bulk-weights): verified.** The
pairings were checked against Prop. prop:fresh-identity for both starting signs.
For sigma_0 = +: `(q^+_{m+1}, u^-_m, u^+_m, q^-_m)` with weights
`mu_+ * 1 + 1 * mu_- = s`. For sigma_0 = -: `(u^+_m, q^-_{m+1}, q^+_m, u^-_m)`
with weights `1 * mu_- + mu_+ * 1 = s`.

**Step 1, endpoints and outside bins: verified.** `B_N T_sigma(N) -> 0` by
Lemma lem:small. For k <= 0 or k >= N, `|k - pN| >= min(p,1-p)N`, and
`eps_h(cN/B_N) -> 0` because `B_N = o(N)`.

**Step 1, (eq:bulk-factor): verified.** For `8m mu <= eps N` it follows from
(eq:bulk-small) and `C_3 b e <= 1`, which holds eventually since `b <= B` and
`B e -> 0`. For larger m: `C_1/a(m) <= C_1/a(eps N/(8mu)) <= 8C_1/(eps b_{sigma,N})`,
using the limit `(8mu/(eps s))^{1/alpha} < 8/eps` (checked in both cases, whether
the base is `>= 1` or `< 1`). **Asymmetry:** the paper correctly notes that
`C_4/b_{sigma,N}` equals `C_4/B_N` only for the dominant sign. I checked every
later use. The bound is applied only to the factor of sign `tau_N` (Steps 3
and 4), never to the factor of sign `tau-bar`.

**Step 2: verified.** `k_- < eps N` and (K2) force `m <= k_- < eps N`. Then
`8m mu_+ <= 8 eps mu_+ N <= N/2` (since `eps <= 1/(16 mu_+)`), and
`k_+ > (1-eps)N >= N/2` (since `eps <= 1/2`). So Lemma lem:small with `1/2` in
place of eps bounds the plus factor by `C_3(+,1/2) e_{+,N}`. The minus factors
sum to at most 1 for each i by (K1), which needs `k_- >= 1`. Hence
`B_N F <= 2 C_3 B_N e_{+,N} -> 0` uniformly. This uses `B_N e_{+,N} -> 0` even
when + is the sign with the smaller scale, which Section 3 above confirms. The
mirror case and both starting signs are the same. The profile bound
`|k-pN| >= (min(p,1-p) - eps)N >= eps N` holds because `eps <= min(p,1-p)/2`.

**Step 3, (eq:bulk-remote-counts): verified.** The dominant factor is at most
`C_4/B_N` (its level lies in `[eps N, N]`). The other factor's sum over
`m notin I` is bounded by the maximum over both signs of
`sup_{j >= eps N} sum_{m notin I_j} W_m(j)`, whose limsup is at most `eta(K)` by
Lemma lem:index(a). Taking the maximum over the two signs handles a dominant sign
that changes with N. The comment on line 462-465 is accurate: `m > max I` gives
`S^{tau-bar}_m < k_{tau-bar}`, controlled by (iv) through the deterministic
inclusion shown in Section 4.

**Step 3, (eq:bulk-window): verified.** `|k_{tau-bar} - m mu_{tau-bar}| <= K a(N/mu_{tau-bar}) <= eps N/2`
and `eps N <= k_{tau-bar} <= N` give the two bounds.

**Step 3, (eq:bulk-shift): verified by direct computation for both signs.**
- tau = +:
  `[s k - mu_+ N + mu_+(N-k)]/mu_- - m mu_+ = k(s - mu_+)/mu_- - m mu_+ = k - m mu_+`.
- tau = -:
  `[-s k + mu_+ N + mu_- k]/mu_+ - m mu_- = N - k - m mu_-`.

**Step 3, (eq:bulk-ratios): verified.** Each limit is strictly below the stated
constant, because `x^{1/alpha} < x` for `x > 1` and `x^{1/alpha} < 1` for `x < 1`.
The third inequality involves `tau_N`, but it holds eventually for each fixed
sign, so it holds for `tau_N` for N past the larger of the two thresholds.

**Step 4: verified apart from one missing restriction (gap B1).**
- For `m in I`: `|k_{tau-bar} - m mu_{tau-bar}| <= K a(N/mu_{tau-bar}) <= c_0 K b_{tau-bar,N} <= c_0 K B_N`.
  With `c_0 K = sR/(2 mu_max)`, (eq:bulk-shift) gives
  `|k_tau - m mu_tau| > sRB_N/mu_{tau-bar} - (mu_tau/mu_max) sRB_N/(2mu_{tau-bar}) >= sRB_N/(2mu_{tau-bar})`.
  Correct.
- `a_tau(m) <= a_tau(2N/mu_min) <= c_1 b_{tau,N} = c_1 B_N`. This uses
  dominance, because `b_{tau,N} = B_N`. So `|z| >= sR/(2 c_1 mu_{tau-bar}) >= kappa R`.
- `B_N/a_tau(m) <= c_2`, because `m >= eps N/(2 mu_max)` and
  `B_N = a_tau(N/s) <= c_2 a_tau(eps N/(2 mu_max))`. This also uses dominance.
  For the other sign, `B_N/a_{tau-bar}(m)` is about `1/theta_{tau-bar,N}`, which is
  unbounded. The proof never uses that ratio. The asymmetry is respected.
- `c_W g(z) <= mu_max g-bar(kappa R)`, and `delta(m) <= delta(ceil(eps N/(2mu_max)))`
  because m is an integer `>= eps N/(2 mu_max)` and delta is a tail supremum.
- The `tau-bar` factors sum to at most 1 per i by (K1). Then
  `D_N <= B_N F + h_N(x)` with `h_N(x) <= eps_h(R)` for `|x| > R`. Adding
  (eq:bulk-remote-counts) gives `rho(R)`, and `rho(R) -> 0`.

**My own derivation of the remote-bin bound.** I keep K free instead of tying it
to R. For `m in I`,
`|k_tau - m mu_tau| >= (s R B_N - mu_max c_0 K B_N)/mu_{tau-bar}`, so
`|z| >= (sR - mu_max c_0 K)/(c_1 mu_max)` for `R > mu_max c_0 K/s`. This gives
`limsup sup D_N <= 2c_2 mu_max max_sigma g-bar((sR - mu_max c_0 K)/(c_1 mu_max)) + 2C_4 eta(K) + eps_h(R)`.
Letting R go to infinity and then K go to infinity gives the same conclusion.
The paper's coupling `K = K(R)` is a special case of this, and the two agree.
The decoupled version also avoids gap B1.

---

## 6. Gaps, ranked by severity

### A. Breaks the theorem
None found.

### A'. Breaks the uniformity
None found. Every error term is a maximum over the two signs of a quantity that
does not involve theta_N. `B_N e_{sigma,N} -> 0` holds for the sign with the
smaller scale (Section 3). The `C_4/B_N` bound is used only for `tau_N`.

### B. Fixable in one line

**B1. Step 4, line 497: `K(R)` can be below 2.** The paper puts
`K = sR/(2 c_0 mu_max)`. With `c_0 = s/mu_min` this is `K = R mu_min/(2 mu_max)`.
For `R = 1` that gives `K <= 1/2`. Lemma lem:index(a), and so `eta(K)` in
(eq:bulk-remote-counts), is stated only for `K >= 2`. The displayed bound
(eq:bulk-remote-bins) is therefore unproved for `1 <= R < 4 mu_max/mu_min`.
This is a missing hypothesis. It is harmless because only `R -> infinity` is
used. Fix: "Let `R >= 4 mu_max/mu_min`", or decouple K from R as in Section 5.

**B2. Lemma lem:small, line 197: the hypothesis list is inconsistent.** It
assumes only (RV), but it cites Lemma lem:stable(iii), which is stated under
(RV) and (SPAN). The statement itself is true under (RV) alone, because CD (1.6)
needs no aperiodicity. Fix: state (iii) under (RV), or add (SPAN) to
lem:small. Either is harmless for Thm thm:bulk, which assumes both.

**B3. Lemma lem:stable(iii), line 125: wrong justification for `a_m/a(m) -> 1`.**
Potter's bounds do not give this. The correct reason is that asymptotic inverses
of asymptotically equivalent RV functions with positive index are asymptotically
equivalent (BGT Thm 1.5.12). The claim is true. Similarly, the (ii) remark on CD
(2.6) skips the change of normalization from `a_n` to `a(m)`. That step is not
needed, because Ibragimov-Linnik is cited with general constants.

**B4. Section sec:scales: `a_sigma` should be stated as positive-valued.** The
proofs use `a(m) > 0` (`C_1 >= a(1)`, `1/a(1)`, and `a(m)P <= a(m_0)`). An
"increasing function on `(0, infinity)`" could in principle be nonpositive near 0.
Fix: `a_sigma: (0,infinity) -> (0,infinity)`.

### C. Cosmetic

- **C1.** Line 42-46: the first "Potter" fact (`f(x_N)/f(y_N) -> 1` when
  `x_N/y_N -> 1`) is the uniform convergence theorem (BGT 1.2.1). The second
  (`sup_{1<=y<=x} f(y) <= C f(x)`) is BGT 1.5.3 (or 1.5.6(iii) plus the extension
  to compacts). Both are true.
- **C2.** Lemma lem:stable(iv), line 136: "uses only that `X_sigma` is bounded
  below". The finiteness of `C_-` also uses (i).
- **C3.** Lines 139-143: the remark suggests that (iii) handles the "too few
  runs" case of Lemma lem:index. In fact that case is handled by weak
  convergence (i), and (iii) is used only in Lemma lem:small. Step 3's outline
  item states it correctly.
- **C4.** Notation clashes:
  - `C_1`, `C_2` are used in Lemma lem:profile's proof and again in
    lem:kernels/lem:small.
  - `c_1`, `c_2` (eq:bulk-ratios) sit next to the kernel weights `c_W`.
  - V is the truncation level in lem:kernels and also the kernel name
    `V^{+-,i}`.
  - J is the covering index `J_sigma(j)` and also CD's interval.
  - eps is the fixed constant and also the generic parameter of lem:small.
- **C5.** In the lem:kernels proof the truncation of the survival shift is at V
  (not J). The order of limits there (m first, then V and Z) is correct.

---

## 7. Constant dependence (as announced: laws only)

| constant | depends on | check |
|---|---|---|
| `C_LD` | law of `X_sigma` (via CD `C'_0` and `a`) | ok |
| `C_-` | law and the chosen `a_sigma` | ok |
| `u-bar`, `rho`, `C_1` | law, `a_sigma` | ok |
| `C_T`, `C_2` | law | ok |
| `C_P`, `C_{T,eps}`, `C_3` | law, eps | ok |
| eps | `p`, `mu_+-` | ok |
| `C_4`, `c_0`, `c_1`, `c_2`, `kappa` | laws, eps | ok, none involves theta_N |
| `eta(K)` | laws, K | ok |
| `K(R)` | laws, R | ok (but see B1) |
| `N_1`, `N_2(K)`, `N_3` | laws, K | thresholds only |

None depends on N, k, or the ratio of the scales.

---

## 8. Verdict

Theorem thm:bulk, as proved through Steps 1 to 4 (classical inputs, kernel
lemmas, small counts, covering index, ends of the row, indices off the window,
remote bins), is **sound with listed fixes**.

The fixes are B1 to B4, each one line. Without B1, (eq:bulk-remote-bins) is
unproved for small R, but nothing downstream needs small R. I found no false
statement and no gap that affects the limit or its uniformity over the ratio of
the scales.

The points the task flagged all hold up:
- the CD citation is exact, and the vanishing left tail is permitted by CD and
  used correctly in (iv);
- the Chernoff bound is correct line by line;
- the index computation holds for every pair of indices;
- "too many runs" is a fixed-index negative deviation, reached through a
  deterministic inclusion with no independence between count and sum;
- the `C/B_N` factor bound is used only for the dominant sign.
