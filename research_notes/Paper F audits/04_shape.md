# Audit 04: `sec_shape.tex` (global mode, second order in the layer, antimode)

Scope: `paperF/sec_shape.tex` (as of 2026-10-24, 707 lines), read against the
macros in `problem131_levy.tex`, all of `sec_setting.tex`, and the statements of
Theorem `thm:bulk`, Theorem `thm:bigjump` (statement taken as given) and
Theorem `thm:preparation`(b). I checked every proof by hand. The exact identities
were recomputed symbolically and the numerical claims recomputed independently.
No file in the paper was edited.

Scripts: `scripts/shape/sym_check.py` and `scripts/shape/num_check.py` in this folder, run with `py -I`.

---

## 0. Summary

The section is in good shape. Every proof I checked closes, with one real gap
and a set of small fixes.

* **One real gap (G1).** The "far" lower bound `eq:anti-far` in the proof of
  Theorem `thm:antimode` uses Theorem `thm:bigjump`(b) on the range
  `pN + K B_N <= k <= N`. The theorem as stated only covers
  `pN + K lambda_N B_N <= k <= N`. When `theta_{+,N} -> 0` (for example
  `alpha_+ > alpha_-`), the strip `K B_N <= k - pN < K lambda_N B_N` is covered
  by neither `thm:bigjump`(b) nor `thm:bulk`(c). The conclusion is true, and the
  proof of `thm:bigjump`(b) already contains what is needed (Section 2, G1), but
  the paper as written does not supply it.
* Everything else is sound, or sound after small, mechanical fixes. Most of these
  are notation collisions caused by the rewrite (`lambda_N`, `kappa`, `C(.)`,
  `M_N`, `mu`, `T`).
* All exact identities check out symbolically for `N <= 6`, with symbolic `f_+`
  and `f_-`. All the numbers in the section reproduce: the `C(j)/j` table, the
  second-renewal ratios, Table `tab:antimode`, `C(phi)`, and the elementary bound
  0.9514.
* Both primary sources the section relies on (Frenk 1982 Lemma 4, and de Bruijn
  and Erdős 1953 Theorem 1) say what the paper says they say.

---

## 1. Recomputations

### 1.1 Lemma `lem:final-explicit` and the identities behind it (exact, symbolic)

Setup: `f_+(1..6)` and `f_-(1..6)` are independent symbols, and the tail mass
beyond 6 is a separate symbol, so `T_s(n) = sum_{m=n}^{6} f_s(m) + t_s7`. For each
`N = 1..6` I compared four computations of the whole row:

1. brute force over all compositions of `N` into alternating runs starting with
   `+`, with weight `f` on complete runs and `T` on the final run;
2. the final-run identity of Proposition `prop:final-run`, with the recursion
   `eq:AB-recursion`, for `0 <= j <= N`;
3. the explicit form `eq:final-explicit` of Lemma `lem:final-explicit`, for
   `0 <= j < N`;
4. the fresh-plus identity of Proposition `prop:fresh-identity`, for `1 <= k <= N-1`.

All four agree identically as polynomials for every `N <= 6` and every bin.
The explicit kernels
`A_t(k) = sum_r u^+_r(k) u^-_r(t-k)` and `B_t(k) = sum_r u^+_{r+1}(k) u^-_r(t-k)`
are right. The change of variables `k = t - j` is right. The claim that only
`r <= j` contributes is right, and so is the case `j = 0` (`P_N(N) = T_+(N)`).

### 1.2 The two smallest bins, fresh plus start

Exactly, and confirmed by the symbolic check for `N = 3..6`:

```
P_N(N-1) = f_+(N-1) + f_-(1) * sum_{a=1}^{N-2} f_+(a) T_+(N-1-a)

P_N(N-2) = f_-(2)   * sum_{a}    f_+(a) T_+(N-2-a)
         + f_-(1)^2 * sum_{a,b}  f_+(a) f_+(b) T_+(N-2-a-b)
         + f_+(N-2) T_-(2)
         + f_-(1) f_+^{*2}(N-2)
```

(The last term in each formula is a censored final minus run.) Under (LR),
writing `alpha = alpha_+` and `mu = mu_+`:

* `sum_a f(a) T(N-i-a) = T(N) (1 + alpha (i + 2 mu)/N + o(1/N))`. The shift of
  the start gives `alpha (i + mu)`, and a giant first run gives `alpha mu`.
* `sum f^{*2}(c) T(N-2-c) = T(N) (1 + alpha (2 + 4 mu)/N + o(1/N))`.
* `f_+(N-i) ~ alpha T(N)/N` and `f^{*2}(N-2) ~ 2 alpha T(N)/N`.

So

```
P_N(N-1)/T_+(N) = f_-(1) + alpha [1 + f_-(1)(1 + 2 mu)]/N + o(1/N)
P_N(N-2)/T_+(N) = u_-(2)
    + alpha [(2 + 2mu) f_-(2) + (2 + 4mu) f_-(1)^2 + T_-(2) + 2 f_-(1)]/N + o(1/N).
```

From `eq:Cj`, with `u(1) = v(1) = f_-(1)`, `u(2) = f_-(2) + f_-(1)^2` and
`v(2) = f_-(2) + 2 f_-(1)^2`:

* `C(1) = alpha [f_-(1) + 2 mu f_-(1) + 1]`. This matches.
* `C(2) = alpha [2u(2) + 2 mu v(2) + 1 + f_-(1)]`. Since `T_-(2) = 1 - f_-(1)`,
  this also matches.

Numerical confirmation (zeta law `n^{-5/2}/zeta(5/2)` on both sides):

| N | `N(P/T - u)` at j=1 | j=2 | j=3 | j=5 |
|---|---|---|---|---|
| 1000 | 6.9877 | 12.0303 | 16.6485 | 25.3809 |
| 8000 | 6.9749 | 11.9540 | 16.4724 | 24.9072 |
| `C(j)` | 6.9731 | 11.9431 | 16.4475 | 24.8406 |

The differences shrink like `1/N`.

### 1.3 Other numbers in the section

* `C(j)/j` at `j = 5, 10, ..., 320`: 4.968, 4.430, 4.041, 3.762, 3.563, 3.422,
  3.323. The limit `6/mu = 3.0811`. All reproduce.
* The ratio in `eq:second-renewal` for the zeta law: 0.9782, 0.9945 and 0.9986 at
  `j = 40, 160, 640`. These reproduce 0.978, 0.994, 0.999. The same computation
  confirms that `u_-` is strictly decreasing with `u_- > 1/mu_-` on `[0, 700]`.
* Table `tab:antimode`: all five rows reproduce exactly (`j*`, `i_N`, `l_N` and
  the last column), computed from `eq:final-explicit`. For `N = 600` I minimized
  over the full range `0 <= j <= 300`. For larger `N` I minimized over
  `j <= 120`, which is well past the minimizer.
* Uniformity check for Proposition `prop:uniform-second`: `(N/j)` times the
  error is about `14.6 j/N` (for example 0.275 at `N = 8000`, `j = 150`, and
  1.36 at `N = 2000`, `j = 150`). So the true remainder is `O(j^2/N^2)`. That is
  `o(j/N)` on `j <= N^{1-eta}`, as claimed, and `o(lambda_N/N)` in the antimode
  window. It is not uniform in `j` up to order `N`, and the proposition does not
  claim that.
* `C(phi) = 0.776131720552733...`. The closed form at `phi` gives the same value,
  `K_phi = phi Gamma(phi^{-2}) = 3.76330...` checks, and `1/C(phi) = 1.288441`.
  The elementary bound evaluates to `0.951361...`. Each of the four inputs checks:
  - `zeta(phi) = 2.238 >= phi + 1/2 = 2.118`;
  - `Gamma(phi) = 0.8957 >= min Gamma = 0.885603...`;
  - `Gamma(phi^{-2}) = 2.326 <= phi^2 = 2.618`;
  - `|cos(pi phi/2)| = 0.8253 <= sqrt3/2`.

  Each bound also goes in the right direction in the formula.
* The power of 2 in the derivation of `C(alpha)`:
  `2^{(1-alpha)/alpha} 2^{-1/alpha} 2^{-1} = 2^{-2}`. Correct.

Not verified: the remark's statement that the computed ratio at `N = 10^5` was
`0.938 C(phi)` "in the earlier version". It cannot be checked from this paper
(see M9).

---

## 2. Gaps, ranked

### G1 (major, fixable from existing material): the strip `K B_N <= k - pN < K lambda_N B_N` in `eq:anti-far`

The proof of `eq:anti-far` says: "By Theorem `thm:bigjump`(b) there is `K` such
that `P_N(k) >= (1-eps) G_N(k)` for `pN + K B_N <= k <= N`." But `thm:bigjump`(b)
is stated on `pN + K lambda_N B_N <= k <= N`, with
`lambda_N = 1 + log(1/theta_{+,N})`. Remark `rem:theta` explains that the
`lambda_N` cannot be dropped from the two-sided statement. The proof then uses
`thm:bulk`(c) only on `|k - pN| <= K B_N`.

When `theta_{+,N}` stays bounded away from 0, `lambda_N` is bounded, and the gap
disappears after enlarging `K`. When `theta_{+,N} -> 0` along a subsequence, the
bins with `K B_N <= k - pN < K lambda_N B_N` and `j = N - k >= delta N` are
covered by neither result. This happens always when `alpha_+ > alpha_-`, which
Theorem `thm:antimode` allows. The bound is needed there for Step 4 of (a) and
for part (b).

The conclusion is true, and the needed one-sided bound is already inside the
proof of `thm:bigjump`(b):

* `eq:giant-split` gives
  `P_N(k) >= C_lambda(k) + I_lambda(k) - E[(G_lambda - 1)^+ 1{A_N = k}]`.
  The no-giant-run term is nonnegative and can be dropped for a lower bound.
* `lem:one-big-run` holds on `L_k >= K B_N`, with no `lambda_N`.
* The two-giant-run term is at most `C K^{-(alpha_+ + 1)/2} G_N(k)` on
  `L/b_{+,N} >= L/B_N >= K`, by "Large j" in that proof. That step uses no
  `lambda_N`.

Only the upper bound, through Lemma `lem:no-big-run`, costs the logarithm.

Fix: add to Theorem `thm:bigjump` (or as a corollary after its proof) the
one-sided statement

    lim_K liminf_N inf_{pN + K B_N <= k <= N, G_N(k) > 0} P_N(k)/G_N(k) >= 1,

and cite that in `eq:anti-far`. A self-contained alternative is the censored-run
lower bound from `eq:final-explicit`:

    P_N(N-j) >= T_+((1-delta)N) * sum_r u^-_r(j) P(S^+_r <= N-j-1)

for `j >= delta N`. One then shows that the probability is `1 - o_K(1)` on
`L_k >= K B_N`, using the spread of the plus sum and of the number of minus runs.
This takes more work than the corollary.

Since `sec_bigjump.tex` is in flux, whoever edits it should keep the one-sided
lower bound available on `L_k >= K B_N`.

Side observation, outside this section, offered for whoever audits
`sec_preparation.tex`: `thm:preparation`(c) is stated on `pN + K B_N <= k <= N`
with no `lambda_N`. A fresh plus start is a preparation with
`nu_+ = f_+ = o(T_+)`. So `thm:preparation`(c) would give the additive two-sided
statement on the range that `rem:theta` says is impossible when
`theta_{+,N} -> 0`. Either `rem:theta` or the range in `thm:preparation`(c) needs
reconciling. Nothing in `sec_shape.tex` uses `thm:preparation`(c).

### M1 (minor, notation, introduced by the rewrite): symbol collisions

* `lambda_N` is `1 + log(1/theta_{+,N})` in `eq:lambdaN`, and is silently
  redefined as `a_-(N)` in proof (a) of `thm:antimode`. The redefinition sits in
  the same proof that, through `eq:anti-far`, relies on `thm:bigjump`(b), which
  uses the original `lambda_N`. This is where G1 hides. Rename the antimode scale
  (for example `m_N` or `Lambda_N`; `ell_N` is taken by Table `tab:antimode`).
  `sec_bigjump.tex` also uses `lambda = ceil(eta L_k)`.
* `kappa = 1/(mu_-^2 (alpha_- - 1))` in proof (a) clashes with the boundary
  kernel `kappa^{(sigma_0)}_+`.
* `C(alpha)` (`eq:Calpha`) and `C(j)` (`eq:Cj`) are both written `C(.)`. So
  `C(1)` and `C(2)` are ambiguous. Generic constants `C` also appear next to
  `C(j)` in the same displays, for example `eq:anti-lower`. Rename one of the two
  functions, for example `D(j)` or `c_j`.
* `M_N` is the largest interior bin in Section `sec:mode`, and the largest number
  of plus slots in one run in `sec_bigjump.tex`.
* `mu` means `mu_+` in `lem:local-bigjump`, `lem:sums` and the proofs of
  `thm:second-order` and `prop:uniform-second`, but `mu_-` in the proof of
  `thm:antimode`. `T` means `T_-` in `eq:cover`–`eq:conv-v` and `T_+` four lines
  later. Each switch is declared, but in a section this dense the switching
  invites errors. I found none that propagated.
* `theta` (proof of (b)), `theta_delta`, `theta'` and the scale ratios
  `theta_{s,N}`. This one is harmless.

### M2 (minor): `prop:uniform-second`, the final minus run

"Lemma `lem:local-bigjump` gives `f^{*(r+1)}(N-j) = ...` uniformly in
`r+1 <= J_N`." But the lemma at level `eta` needs `r+1 <= (N-j)^{1-eta}`, and
`J_N = N^{1-eta}` exceeds `(N - N^{1-eta})^{1-eta}`. Use the lemma with `eta/2`,
as the censored part of the same proof already does.

### M3 (minor): `prop:uniform-second`, the side condition for `lem:sums`

The proof fixes `N` with `2 J_N <= x_N`. Lemma `lem:sums` is stated under
`x >= 4 r mu` for both bounds, and it is applied with `x = x_N/2` and
`r <= J_N`, which needs `x_N >= 8 mu J_N`. This holds for large `N`, since
`J_N = o(x_N)`, but it is not what is written. Better: state in `lem:sums` that
the second bound holds for all `x > 0`. Its proof never uses `x >= 4 r mu`.
Also, `alpha E[S_r; S_r > N/2]` in the first display is redundant, though
harmless. The correct accounting is `(C + alpha) E[j + S_r; S_r > x_N/2]`.

### M4 (minor): `thm:antimode`(a), the order of quantifiers

Step 1 says "Fix `0 < eps < K`", while `eps` is chosen in Step 2 and `K` in
Step 3. The "in particular" at the end of Step 1, and the conclusion, both need
`eps < x_* < K`. For `K` this follows automatically: Step 3's choice gives
`K > 4 s x_*/mu_- > x_*`. For `eps` it does not follow from Step 2's choice in
general. Fix: choose `eps` and `K` first, depending only on
`(kappa, c, alpha_±, mu_±)`, with `eps < x_* < K` and the conditions of Steps 2
and 3. Then run Step 1.

### M5 (minor): lower bounds that multiply by a ratio `>= 1`

Several steps go from `R_N >= (T(N-j)/T(N)) (u(j) - C j T(N))` to
`R_N >= u(j) - C j T(N)`, or to a product expansion. This needs
`u(j) - C j T(N) >= 0`. That holds on the ranges used, since
`C j T(N) <= C delta N T(N) -> 0` and `u(j) >= 1/mu` or `u(j) >= 1/mu - theta`,
but it should be said once. In Step 2, the remark `R_N(0) = 1 > 1/mu` should read
`R_N(0) = 1 > 1/mu + (lambda_N/N)(psi(x_*) + 1)` for large `N`, and the same
should be said for the comparison function at `j = 0`.

### M6 (minor): `lem:sums`, real arguments

`T(x)` is used at real `x` (`x/2`, `x_N/4`). Say once that `T(x)` means
`P(X >= x)`. Also, `T(x/2) <= C T(x)` for all `x >= 4` uses `T > 0`, which (RV)
gives.

### M7 (minor, global): citations and bibliography

All `\ref` and `\eqref` in the section resolve. Forward references
(`eq:second-renewal` at line 434, `eq:conv-v` at line 226) are flagged with
"below", which is fine. Every lemma is stated before it is used. But the
bibliography is empty, so every `\cite` is undefined: `bgt1989`, `dlmf`,
`feller1968`, `frenk1982`, `rogozin1973`, `doney2023` and `debruijnerdos1953`.
The section cites `feller1968` (Vol. I, XIII.3, which is correct for the renewal
theorem), while `sec_bulk.tex` cites `feller1971`. Both can stay, but both must
be entered.

### M8 (minor): cite the classical local big-jump theorem next to `lem:local-bigjump`

The lemma is a special case of Doney's local large-deviation theorem (R. A. Doney,
"A large deviation local limit theorem", Math. Proc. Cambridge Philos. Soc. 105
(1989) 575–577). That theorem gives `P(S_r = r mu + x) ~ r P(X = x)` uniformly in
`x >= gamma_r a_r` with `gamma_r -> infinity`, under
`P(X = n) ~ n^{-1-alpha} L(n)`, which is exactly (LR). Here
`x = n - r mu ~ n >> a_r`, because `r <= n^{1-eta}`, and `f(n - r mu) ~ f(n)` by
the uniform convergence theorem. See also Denisov, Dieker and Shneer (Ann. Probab.
2008) for local versions in the big-jump domain. The in-paper proof is complete,
so the citation is for attribution only.

### M9 (cosmetic): "earlier version of this work"

Lines 169–173 and Remark `rem:ties` refer to an unpublished earlier version, and
the figure `0.938 C(phi)` at `N = 10^5` rests on it. Either cite it properly or
give the number as computed here, with its method. An exact `P_N` row at
`N = 10^5` is out of reach of the `O(N^3)` recursion, so say how it was
obtained.

---

## 3. Statement-by-statement review

### Lemma `lem:profile-uniform`. Sound.
The total-boundedness argument is correct.

### Theorem `thm:mode`
* (a) Sound. `thm:preparation`(b) gives the interior uniform error. The
  common-modulus argument gives `max_k h_N(x_k) >= H_N - omega(1/B_N)`. The
  localization `|x_{k_N}| <= K` and the convergence to the maximizer set are
  correct.
* (b) Sound.
* (c) Sound. The step `B_N in RV_{1/alpha_*}` for equal indices (via the ratio
  sandwich) is correct.
* (d) Sound. The bulk criterion holds for the stationary start. Karamata gives
  `Q_s(N) ~ N T_s(N)/(s(alpha_s - 1))`, so `rho_s = alpha_s - 1`, and the
  golden-ratio threshold follows. For equal pure power laws: `mu = zeta(alpha)`,
  `B_N = (N/s)^{1/alpha}`, `c_alpha = 2^{1-alpha} K_alpha |cos(pi alpha/2)|`, and
  `H_N = h(0) = Gamma(1 + 1/alpha)/(pi c_alpha^{1/alpha})`. All of these are
  correct, as is the constant `C(alpha)`. The specialization at `phi` (using
  `alpha - 1 = 1/phi`, `1 + 1/alpha = phi`, `1 - phi = -1/phi` and
  `2 - phi = phi^{-2}`, which give `K_phi = phi Gamma(phi^{-2})`) is correct.
  - **Direction:** `C(phi) < 1` means that the endpoint atom is smaller than the
    largest interior bin. At the golden ratio the center (interior) wins, by the
    factor `1/C(phi) = 1.2884`. This is consistent with (b) and with `rem:ties`.
  - The fresh-start clause is correct.

  The sentence about two equal laws ("symmetric and unimodal") is true:
  symmetric stable densities are unimodal. It is not needed, since `H_N = h(0)`
  is proved directly by Fourier positivity.

### Remark `rem:ties`. Sound.
The `0.938` figure is unverified (M9).

### Lemma `lem:final-explicit`. Sound.
Verified symbolically for `N <= 6` (Section 1.1).

### Identities `eq:cover`, `eq:cover-v` and `eq:conv-v`. Sound.
The identity `eq:cover-v` is a covering-index argument: the covering run has
index `r + 1`, and `r = #{i >= 1 : S_i <= j - 1}`. The two forms of `eq:Cj` agree
by `eq:conv-v`. Also, `C(j) = alpha [j u(j) + mu_+ v(j) + gamma^{(+)}_+(j)]`. This
is consistent with the big-jump kernel `eq:gamma`, which is a good cross-check.

### Lemma `lem:local-bigjump`. Sound, under (LR) alone, with `1 < alpha < 2`.
Hypothesis actually used:

* `f in RV_{-alpha-1}`, from (LR) and (RV);
* `alpha > 1`, for the Markov steps and for `r T(n) -> 0`;
* `alpha < 2`, for `E[X^2; X <= y] <= C y^2 T(y)`.

No aperiodicity is needed, since `f(n) > 0` eventually. The uniformity is
uniformity in `1 <= r <= n^{1-eta}` for each fixed `eta`.

Detailed check:

* **One large run (`E_1`).** The upper bound splits at `w_n = n^{1-eta/2}`. Markov
  gives `P(S_{r-1} > w_n) <= mu n^{-eta/2}`, and `f(n-w) <= C_eps f(n)` for
  `n - w > eps n`. The lower bound keeps `w <= w_n` and
  `max_{i<r} X_i <= y`, at a cost of at most `rT(y) -> 0`. Correct.
* **Two or more large runs.** Conditioning on all runs except one large one
  bounds the probability for a fixed pair by `T(y) sup_{x>y} f(x)`. There are at
  most `r^2` pairs, and `r T(n) -> 0` uniformly, so this part is `o(r f(n))`.
  This covers every configuration with at least two summands above `eps n`.
* **All summands at most `eps n`.** This includes configurations where all
  summands are of order `n/r`, which is the case the brief asks about. Bounding
  the local probability by a tail probability of one half loses at most a factor
  of order `n`. The truncated exponential Chebyshev bound recovers it: it gives
  `(e Lambda^{-1 + q mu/x})^{1/(2 eps)}` with `Lambda >= c_eps/(r T(n))`, so
  `E_3 <= C_eps (r T(n))^{1/(4 eps)}`. This beats `r f(n) >= c r T(n)/n` once
  `eps < gamma/(4(1 + gamma))`, with `r T(n) <= n^{-gamma}`. I rechecked the
  algebra:
  - the inequality `e^z <= 1 + z + z^2 e^{lambda y}/(lambda y)^2` on
    `[0, lambda y]`;
  - the identity `q e^{lambda y} b/y^2 = x/y = 1/(2 eps)`;
  - `q mu/x <= 1/2`;
  - `Lambda >= 1`, so that `lambda >= 0`.

  All are correct.

The proof is complete. For comparison with the literature, see M8.

### Lemma `lem:sums`. Sound.
See M3 and M6 for presentation.

### Theorem `thm:second-order`. Sound.
* **Dominated convergence at fixed `j`.** Over the finitely many `r <= j`, the
  dominating function `C(j + S_r)` is integrable, using `g_N(x) <= Cx` on
  `x <= 3N/4`. Correct.
* **Start of the censored run.** The expectation of the start position gives
  `alpha (j + r mu_+)`. Correct.
* **Complete-run term.** When an earlier plus run is giant,
  `sum_{l < N/2 - j} f^{*r}(N-j-l) T(l)` with `sum_l T(l) = mu_+` gives
  `alpha r mu_+`. The bound `f^{*r} <= 2 r f` comes from `lem:local-bigjump` at
  fixed `r`. Correct.
* **Final minus run.** The term `(r+1) alpha T/N`, together with `eq:cover` and
  `eq:cover-v`, gives `sum_{i<j} u(i)`. Correct.
* **Green identity.** It enters only in the interpretation of the second form,
  which is correct.
* **Two giant runs.** These are inside the `l`-sum and the `P(S_r > N/2)` bound
  (`C r T(N) = o(1/N)`). Since `r <= j` is fixed, they cost `o(1/N)`. Correct.
* **The limit.** `C(j)/j -> 2 alpha_+ s/mu_-^2` by the renewal theorem and
  Cesàro, using `eq:conv-v`. Correct.
* The remark that the convergence error is of order `j T_-(j)` is correct: the
  Cesàro term is `~ kappa j T_-(j)/(2 - alpha_-)`.

### Proposition `prop:uniform-second`. Sound with fixes M2 and M3.
I checked the dependence of every estimate on `j`:

* the censored term errors are `o(j + r)`, uniformly in `r <= j <= J_N`;
* `P(S_r > N/2) T(N)` sums to `O(v(j) T(N)) = o(j/N)`, because
  `v(j) <= j u(j) <= j` and `N T(N) -> 0`;
* the `l`-sum uses `lem:local-bigjump` at `eta/2` with `r` up to `J_N`, which is
  legitimate;
* the final minus run is `o(sum_{i<j} u(i)/N) = o(j/N)`.

The number of minus runs before the giant run (`r` up to `j`) is handled by the
weights `u^-_r(j)`, whose sums `u(j) <= 1` and `v(j) <= j` keep every error at
`o(j/N)`. The `o(j/N)` is genuinely uniform. Numerically the remainder is
`O(j^2/N^2)` (Section 1.3).

### Second-order renewal input `eq:second-renewal`. Correct as cited.
I read the primary text of Frenk, Adv. Appl. Probab. 14 (1982) 870–884,
downloaded from repub.eur.nl. Lemma 4 on p. 873 states:

> `1 - F(n) in RV_{-alpha}` (`alpha > 1`) if and only if
> `u_n - 1/mu in RV_{1-alpha}`. Both imply
> `lim (u_n - 1/mu)/(n(1 - F(n))) = 1/(mu^2(alpha - 1))`.

The setting is a persistent, aperiodic recurrent event; aperiodic means gcd 1,
which is (SPAN). The proof goes through `lambda_n ~ -(1 - F(n))/mu^2` (Wiener's
theorem) and
`u_n - 1/mu = (1/mu^2) sum_{k > n} (1 - F(k)) (1 + o(1))`. With
`1 - F(n) = P(X > n) = T(n+1) ~ T(n)`, this is exactly `eq:second-renewal`. I did
not check Rogozin 1973 or Doney 2023 "Theorem 1". They are only "see also"
citations.

### Lemma `lem:logconvex`. Sound, and the citation is exact.
I read the primary text of de Bruijn and Erdős, J. Res. NBS 50 (1953) 161–164.

* Theorem 1 assumes `c_{k-1} c_{k+1} > c_k^2` for every `k > 1` (strict) and
  concludes `f(n-1) f(n+1) > f(n)^2` for every `n > 1`.
* Their recursion has `f(n) = u(n-1)`: their check
  `f(1) f(3) - f(2)^2 = c_2 f(1)` fixes the shift. So the conclusion is
  `u(m-1) u(m+1) > u(m)^2` for `m >= 1`, exactly as stated in the paper.
* Their remarks after Theorem 1 contain the paper's ratio argument verbatim.
* Their hypothesis forces `c_k > 0`, so the paper's extra hypothesis
  `f_-(n) > 0` is harmless.

Strictness is used, and it is available.

### Theorem `thm:antimode`
* **The two lower bounds.**
  - `eq:anti-lower` is sound. It uses `T(N-j-S_r) >= T(N-j)` and
    `P(S_r >= N/2) <= C r T(N)` for `r <= j <= N/(8 mu_+)`. The monotonicity of
    `T(n)/n` gives `T(N-j)/T(N) >= 1 + (3/4) alpha j/N`.
  - `eq:anti-far` has gap G1 in the strip
    `K B_N <= k - pN < K lambda_N B_N` when `theta_{+,N} -> 0`. Elsewhere it is
    sound. In particular `G >= T_+(L_k) u(j)` with `L_k <= (1-delta) N` is right,
    and `B_N T_+(N) -> 0` handles the bulk part.
* **(a), the scaling limit.**
  - The window expansion `eq:anti-window` follows from `prop:uniform-second`
    (with `K lambda_N <= N^{1-eta}`, `1 - eta > 1/alpha_-`),
    `eq:second-renewal` with the uniform convergence theorem, and
    `C(j) = c j (1 + o(1))`.
  - `psi` is strictly convex, and its minimizer satisfies
    `x_*^{-alpha_-} = c mu_-^2 = 2 alpha_+ s`, which gives
    `T_-(j*_N) ~ 2 alpha_+ s/N`. Correct.
  - Steps 2–4 and the conclusion are correct, modulo M4 and M5, and modulo G1 in
    Step 4.
  - The comparison minimizer `i_N` is handled correctly (`C(j) >= alpha_+ j/mu_-`
    under `u > 1/mu_-`).
  - Step 2's Potter bound is correct: take `delta = (alpha_- - 1)/2`.
* **(b).** Correct, given `eq:anti-far` (so G1 applies). Here
  `m_* = min u < 1/mu_-` is attained on a finite set. The middle range uses
  `eq:anti-lower` and `N T_+(N) -> 0`, and the fixed `j` use
  `thm:second-order` (`thm:bigjump`(a) would also do). Only a weaker far bound is
  needed in (b): anything above `m_* + theta`.

### Remark `rem:shape-words`. Consistent with the theorems it cites.

### Table `tab:antimode`. Reproduced exactly.

---

## 4. Verdicts

| Statement | Verdict |
|---|---|
| Lemma `lem:profile-uniform` | Sound |
| Theorem `thm:mode` (a)–(c) | Sound |
| Theorem `thm:mode` (d), incl. `C(alpha)`, `C(phi) = 0.77613 < 1`, bound 0.9514 | Sound. At `phi` the interior (center) wins by `1/C(phi) = 1.2884` |
| Remark `rem:ties` | Sound. The `0.938 C(phi)` figure is unverified (M9) |
| Lemma `lem:final-explicit` | Sound (symbolically verified, `N <= 6`) |
| Identities `eq:cover`, `eq:cover-v`, `eq:conv-v` | Sound |
| Lemma `lem:local-bigjump` | Sound under (LR) with `1 < alpha < 2`, uniform in `r <= n^{1-eta}`. Cite Doney 1989 (M8) |
| Lemma `lem:sums` | Sound (fixes M3 and M6 are presentational) |
| Theorem `thm:second-order` | Sound. `C(1)` and `C(2)` match the exact small-bin expansions |
| Proposition `prop:uniform-second` | Sound with fixes M2 and M3 |
| `eq:second-renewal` (Frenk 1982 Lemma 4) | Correctly cited and correctly transcribed |
| Lemma `lem:logconvex` (de Bruijn–Erdős Theorem 1) | Sound, and the citation is exact |
| Theorem `thm:antimode` (a) | Conditional on a one-sided lower bound `P_N(k) >= (1 - o_K(1)) G_N(k)` on `L_k >= K B_N` (G1). When `theta_{+,N}` is bounded away from 0 it is sound now, with M4 and M5 |
| Theorem `thm:antimode` (b) | Same condition (G1). Sound otherwise |
| Internal consistency | All labels resolve. No lemma is used before it is stated. Notation collisions are listed in M1. Bibliography empty (M7) |

**Exact remaining gap.** The proof of `eq:anti-far` needs, for each `eps > 0`, a
`K` such that `P_N(k) >= (1 - eps) G^{(+)}_N(k)` for all large `N` and all
`k >= pN + K B_N` with `N - k >= delta N`. Theorem `thm:bigjump`(b) as stated
gives this only from `pN + K lambda_N B_N`. The missing strip is nonempty exactly
when `theta_{+,N} -> 0`. The bound follows from `eq:giant-split`,
`lem:one-big-run` and the two-giant-run estimate in the existing proof of
`thm:bigjump`(b), none of which uses `lambda_N`. It needs to be stated and cited.
