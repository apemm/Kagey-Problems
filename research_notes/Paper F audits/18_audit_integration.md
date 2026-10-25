# 18. Audit of the integrated window and modes material in Paper F

October 25, 2026. Read: `paperF/sec_bigjump.tex` (Section 4.5: `thm:window`, `lem:laplace`,
`lem:tilt`, `rem:window-conj`, and the text after Theorem B and in `rem:theta`),
`paperF/sec_shape.tex` (Section 6.4: `lem:diff-renewal` to `conj:three-modes`, together with
`thm:mode`, `thm:second-order`, `lem:logconvex`, `thm:antimode`), `sec_preparation.tex`
(Theorem C), `sec_setting.tex` (hypotheses, `prop:fresh-identity`, `eq:q-cover`), the abstract
and the introduction. I compared these with `Paper F window O2/01_report.md` and `02_audit.md`,
`Paper F modes O1/01_report.md`, `02_report.md` and `03_audit.md`, and with note 17. Nothing in
the paper was edited.

## Verdicts

| Item | Verdict |
|---|---|
| 1. Lower bound `M_+ + M_- + 1` without the no-ties hypothesis | proved as written |
| 2. `cor:four-modes` (prepared log-convex start, at least four modes) | proved as written; the exact law agrees |
| 3. One local maximum iff `u_-` nonincreasing, fresh plus start only | proved as written. Note 17 is right that 03 overstated it, but note 17's minus-start example does not work as given |
| 4. Statements of `thm:window` and `thm:ends` against the audited versions | `thm:window` matches O2 with all its restrictions. `thm:ends` holds as stated, but the proofs of (d) and of the minimizer clause are each one step short (fix below) |
| 5. (LD), `lem:plus-diff` and `thm:first-diff` (M1) | proved as written |

## 1. The lower bound `M_+ + M_- + 1` (`prop:copy`(b), `thm:modes-lower`)

**Claim card.** Hypotheses: (RV) and (SPAN) for both signs, `nu_sgn = o(T_sgn)` for both
signs, and both limits `kappa~_sgn(0)` exist. Conclusion: each end profile has finitely many
local maxima, at least one, and for large `N` the law `P_N` has at least `M_+ + M_- + 1` modes.
Local maxima are maximal constant blocks, endpoints count, and plateaus count once. There is no
no-ties hypothesis.

**Critical step, derived independently.** Let `{a..b}` be a local maximum of `kappa~_+` with
value `y`. Its neighbours `a-1` (when `a >= 1`) and `b+1` take values different from `y` and
no larger, so they are at least `3 eps` below `y` for some `eps > 0`. By `eq:profile-limit`, for
large `N` the ratio `R_N(i) = P_N(N-i)/T_+(N)` is within `eps` of `kappa~_+(i)` for
`a-1 <= i <= b+1`. Then `max R_N` on `{a..b}` is at least `y - eps`, and both neighbours are at
most `y - 2 eps`. Let `k` be the index of a maximum of `P_N` on `{N-b..N-a}`. The maximal
constant block of `P_N` that contains `k` cannot reach `N-b-1` or `N-a+1`, because those
values are strictly smaller. Inside the interval its neighbours are no larger than the maximum
and differ from it. So the block is a local maximum of `P_N` inside `{N-b..N-a}`. If `a = 0`,
the index `N` is the last index of `P_N`, which lives on `{0..N}` by `prop:fresh-identity`, and
the endpoint rule applies. Ties never enter.

**Implications checked.**
- `lem:prep-diff` with `c = 0`: the generating function `pi_+(U-1) + nu^_- U` gives
  `kappa_+(n) - kappa_+(n-1) = pi_+ d_n + (nu_- * d)_n` for `n >= 2`. Applying
  `eq:product-rule` with `a = nu_-` (sum `pi_-`, ratio limit `c`) and `b = d` (sum
  `1/mu_-`, ratio limit `-1/mu_-^2`) gives `(c mu_- - 1)/mu_-^2`. With `c = 0` and
  `T_- > 0` everywhere (unbounded support under (RV)), `kappa~_+` is strictly decreasing on
  some `[J, inf)`.
- So every local maximum is a block inside `[0, J]`. There are finitely many, and the block of
  a global maximizer (attained in `[0, J]`) is one of them, so `M_+ >= 1`.
- Distinct local maxima are disjoint blocks, so the copies lie in disjoint index sets and are
  distinct modes.
- The bulk mode: `nu = o(T)` and `B_n T_sgn(n) -> 0` give the bulk criterion. By `thm:mode`(a)
  every interior maximizer lies in `pN + O(B_N)`. The constant block through one of them
  consists of interior maximizers, so it stays in `pN + O(B_N)`. Its neighbours are interior,
  no larger than the maximum and different from it, so the block is a mode. It is far from the
  two end blocks `{N-J..N}` and `{0..J}`.
- The hypotheses of `eq:profile-limit` (Theorem C(d) needs only (RV) for the plus sign, and
  `nu_+ = o(T_+)` turns it into a limit; `j = 0` uses `P_N(N) = Q_+(N)`) are all assumed.

Dropping the no-ties hypothesis is legitimate.

## 2. The prepared log-convex start (`cor:four-modes`)

**Claim card.** Hypotheses: (RV) and (SPAN) for both signs, and `f_-` strictly log-convex with
`f_- > 0` (`lem:logconvex`). The initial run is fresh plus with probability 1/2, and a minus
run of fixed length `d_0 >= 2` with probability 1/2. Conclusion: at least four modes for large
`N`, and for a fresh plus start the profile is strictly decreasing.

**Critical step, derived independently.** Here `pi_+ = 1/2` and `nu_- = (1/2) delta_{d_0}`,
so by `eq:kappa-prep` `kappa~_+(j) = (u(j) + u(j - d_0))/2` for `j >= 1`, with `u = u_-` and
`u = 0` at negative arguments. Also `Q_+(N) = T_+(N)/2`, so `kappa~_+(0) = 1/2`. Since
`d_0 >= 2`, `kappa~_+(1) = u(1)/2 = f_-(1)/2 < 1/2`, so `{0}` is a local maximum. Next,
`kappa~_+(d_0) = (1 + u(d_0))/2`. This exceeds `u(1)/2` because `u(1) < 1`. It exceeds
`1/mu_-` because `u(d_0) > 1/mu_-` by `lem:logconvex` and `1 >= 1/mu_-`. The profile tends to
`1/mu_-` (Remark `rem:kappa-prep`). So the supremum over `j >= 1` is attained, only at indices
`j >= 2`. The constant block through such an index cannot reach `j = 1`, so its left neighbour
has index at least 1, and it is a second local maximum. So `M_+ >= 2`. At the minus end
`kappa~_-(0) = 0` (for `N > d_0`), so it exists, and `M_- >= 1`. `nu_+ = f_+/2 = o(T_+)` since
`T_+(n+1)/T_+(n) -> 1`, and `nu_-` vanishes beyond `d_0`. So `thm:modes-lower` applies and gives
at least `2 + 1 + 1` modes. The fresh-plus clause follows from `u(1) = f_-(1) < 1` and the
strict decrease of `u` in `lem:logconvex`.

**Numerical spot-check.** My own scripts are in my scratch folder (`audit18/modes.py` and
`run.py`) and were run with `py -I`. The exact law is computed by a column recursion over the
number of minus steps, using `B_-(k, j)` and `B_+(k, j)`, the probabilities of a run boundary
after `k` plus and `j` minus steps followed by a minus or a plus run. The recursion is
`B_+(., j) = init + sum_x B_-(., j-x) f_-(x)` and `B_-(., j) = init + B_+(., j) *_k f_+`, and the
law is read off from the run that covers step `N`. This route differs from
`prop:fresh-identity` and from `verify_modes.py`. It was checked against a step-by-step chain on
(sign, age, count) at `N = 7, 12` (largest difference `4e-16`). The runs use the zeta law
`f(n) = n^{-5/2}/zeta(5/2)` for both signs, which is strictly log-convex. Modes are listed as
values of `k`.

| d_0 | profile maxima | N = 300 | N = 1000 | N = 2000 | smallest relative gap between neighbours |
|---|---|---|---|---|---|
| 2 | j = 0, 2 | 1, 150, 298, 300 | 1, 500, 998, 1000 | 1, 1000, 1998, 2000 | >= 4.6e-5 |
| 3 | j = 0, 3 | 1, 150, 297, 300 | 1, 500, 997, 1000 | 1, 1000, 1997, 2000 | >= 1.8e-6 |
| 5 | j = 0, 5 | 1, 149, 295, 300 | 1, 499, 995, 1000 | 1, 999, 1995, 2000 | >= 6.3e-5 |
| 8 | j = 0, 8 | 1, 148, 292, 300 | 1, 498, 992, 1000 | 1, 998, 1992, 2000 | >= 1.4e-5 |

In every case there are exactly four modes, and they sit where the corollary and Theorem
`thm:modes-lower` put them. The `d_0 = 5`, `N = 1000` row reproduces the paper's numbers
(1, 499, 995, 1000). The total mass error is below `3e-13`, and every relative gap is many
orders of magnitude larger than that. `R_N(0..d_0+2)` approaches `kappa~_+`. For example, for
`d_0 = 5` the value at `j = 5` is 0.871, 0.830 and 0.822 at the three `N`, against the limit
0.8139.

## 3. One local maximum iff `u_-` nonincreasing

**Claim card (paper, after `thm:modes-lower`).** For the fresh plus start,
`kappa~_+ = (1, u(1), u(2), ...)` has exactly one local maximum iff `u` is nonincreasing on
`j >= 1`.

**Derivation.** (If) `u(1) = f_-(1) < 1`, since (RV) forces unbounded support. So
`1 > u(1) >= u(2) >= ...`, and `{0}` is a local maximum. A block starting at `a >= 1` has a left
neighbour that is no smaller, so it is not a local maximum. (Only if) Suppose `u(j+1) > u(j)`
for some `j >= 1`. By `lem:diff-renewal`, `u` is strictly decreasing from some `J` on, so
`sup_{i > j} u(i)` is attained, at a value `M > u(j)`. The constant block through a maximizer
lies in `[j+1, inf)`, since `u(j) < M`. It is finite, because of the strict decrease, and both of
its neighbours are below `M`. So it is a second local maximum, distinct from `{0}`. The claim is
proved as written.

**Which audit is right.** Note 17 is right, and 03 (line 112, "checks for all three starts")
and 01 section 4 overstate the claim. The paper's fair zeta example does not test the
equivalence: there `u` is strictly decreasing, and `(1/2, 0.745, ...)` has one local maximum,
which agrees with it. Note 17's fair example is a true counterexample to the "only if" half: `f(1) = 0.6`, `f(2) = 0.3`, with a zeta tail of mass 0.1 from `n = 3`.
I computed `u(1..3) = 0.6, 0.66, 0.615`, which then decreases up to `j = 3000`. The profile
`(1/2, u(1), ...)` has one local maximum, at `j = 2`, while `u` is not monotone.

**Caveat on note 17.** Its minus-start example, "`f(1) = 0.1`, `f(2) = 0.5`", only shows that
`u` rises. With a zeta tail of mass 0.4 from `n = 3`, `u` oscillates (0.1, 0.51, 0.257, 0.372,
0.296, ...), and `(0, u(1), ...)` has five local maxima, at `j = 2, 4, 6, 8, 10`. So the example
does not show what it claims. The claim itself is true, since it is conditional on `u` rising
and then falling. A working example is `f(1) = 0.2`, `f(2) = 0.3`, with a zeta tail of mass 0.5
from `n = 3`. Then `u = 0.2, 0.34, 0.323, ...`, strictly decreasing on `[2, 3000]` (checked
numerically, with the tail covered by `lem:diff-renewal`). The profile has one local maximum,
at `j = 2`. This example is not in the paper, so the paper needs no change.

## 4. Statements against the audited versions

### `thm:window`

**Claim card.** Hypotheses: (RV) and (SPAN) for both signs, (LR) for the plus sign, a fresh
start, and `b_{+,N} <= b_{-,N}` for large `N`. (a) For every `eps` there is `K` such that, on
`K <= x <= X_N` with `X_N B_N = o(N)`,
`max{(1-eps)G_N, e^{-(1+eps)I_N}/B_N} <= P_N <= (1+eps)G_N + e^{-(1-eps)I_N}/B_N`.
(b) gives the limit `varkappa_-(x/p)^{beta_-}`, the Potter bounds, the scaling, and the
pure-power form. (c) assumes `theta_+ -> 0` and shows that the ratio `P_N/G_N` tends to 1
from `(1+delta)xi_N B_N` on and to infinity on `[K_0, (1-delta)xi_N]`, with
`xi_N = (log 1/theta_+)^{(alpha_- - 1)/alpha_- + o(1)} = o(lambda_N)`.

**Comparison.** The statement matches Theorem O2 of 01 and the claim card of 02 item by item.
- `I_N(x) = I(n_N, xB_N/p) = n_N psi*(xB_N/(p n_N))` equals O2's `Lambda_N(x)`.
- `xi_N` is O2's `x*_N`, defined by the same equation `I_N = alpha_+ log(1/theta_+)`.
- `varkappa_- = (alpha-1) alpha^{-beta} K_alpha^{-1/(alpha-1)}` equals `c_Z`.

I checked the balance myself. `sup_u(uy - K u^alpha)` at `y = x/p` gives `varkappa_- y^beta`.
Equating it with `alpha_+ log(1/theta_+)` gives the stated exponent `1/beta = (alpha-1)/alpha`
and the pure-power constant. Also `beta_- > 2` because `alpha_- < 2`, which gives
`xi_N = o(lambda_N)`.

**Restrictions.**
- **No claim of "no window".** `grep` finds no such phrase. After Theorem B the paper says the
  window "shrinks to `K <= x <= (1+delta)xi_N`". The introduction calls the remaining range "the
  exception announced above". The abstract says "locate the start ... up to a factor
  `1 +- delta` and describe the law before it on the logarithmic scale".
- **The strip stays open.** The text after the theorem says it is "not described with a
  relative error", and after Theorem B it "remains open".
- **The fallback in (c1)** uses `X_N = K_1(eps) lambda_N` explicitly, as 02 asked.
- **The log description below the start** (`log(B_N P_N) = -(1+O(eps)) I_N`) follows from (a)
  and `eq:BG-log`. Below `(1-delta)xi_N` the light term exceeds `G_N` by
  `exp(c alpha_+ log 1/theta_+)`, and `log 2 <= eps I_N` once `x >= K(eps)`.

**Renamings.** No `x*_N` or `Lambda_N(x)` survives anywhere in the paper. `Lambda_N = a_-(N)`
and `x_*` are used only in `thm:antimode` and `thm:ends`, with their old meanings. Two minor
overloads are harmless: `delta` names both the Potter exponent in (b) and the strip in (c), and
`X` names both `X_-` and the sequence `X_N` in Section 4.5.

### `thm:ends`

**Comparison.** It matches F2 of 02 and 03 with the restrictions applied.
- The `j*_N` clause is stated only for the fresh plus start with `u_-(j) > 1/mu_-` for all
  `j >= 1`. This is right: `thm:antimode`(a) has exactly this hypothesis, and its proof puts
  `j*_N` (the minimizer over `0 <= j <= (1-p)N`) inside the open window for large `N`.
- For other starts the paper uses minimizers over `[J_+, N^{1-eta}]`.
- (d) is stated as a parity after zeros of `D_N` are deleted.
- Plateaus count once, both in the definition and in the sentence after the theorem.
- Steps (a) to (c) check. The display uses `Delta u(j) = d_{j+1} ~ -T_-(j+2)/mu_-^2`, which
  agrees with `t_n = T_-(n+1)` in `lem:diff-renewal`. Also
  `x_*^{-alpha_-} = 2 alpha_+ s = c_a mu_-^2` with `s = mu_+ + mu_-`, and the range of (c) is
  nonempty because `1/alpha_- <= 1/alpha_* < 1 - eta`.

**The gap in (d) and in the minimizer clause.** Write `L = (x_* - eta')Lambda_N` and
`U = (x_* + eta')Lambda_N`, and let `g(j) = P_N(N-j)`, so `D_N(j) = g(j+1) - g(j)`.
- (b) and (c) give `D_N < 0` up to `floor(L)` and `D_N > 0` from `ceil(U)` on. So the
  odd number of sign changes is proved on `[floor(L), ceil(U)]`, not on the open window
  `(L, U)` as stated. If `D_N > 0` on all of `(L, U)`, there is no sign change inside it.
- Likewise `g` increases strictly from `ceil(U)` on, so a minimizer can sit at
  `ceil(U) > U`, just outside the closed window. The local minimum mentioned in the sentence
  after the theorem can sit there too.

**Missing implication (one line).** Apply (b) and (c) with `eta'/2` in place of `eta'`. For large
`N`, `(x_* - eta'/2)Lambda_N >= ceil(L)` and `(x_* + eta'/2)Lambda_N + 1 <= floor(U)`, so
`D_N(ceil(L)) < 0` and `D_N(floor(U)) > 0`. That gives the parity inside `(L, U)` and puts every
minimizer inside `(L, U)`. The statements are then true as written. The proof sentence "Then (d)
follows ... and so does the statement on minimizers" should mention this step. The same
off-by-one is in 03 (line 184).

**Calibration of the abstract.** The abstract's last sentence ("its only other local extrema up
to distance `N^{1-eta}` are an odd number near the interior minimum") rests on `thm:ends`. That
theorem is proved only for fresh and fair starts with no ties of `kappa~_+` on `[0, J_+)`, and the
abstract leaves out both restrictions. "Near each end the law copies the local extrema of the
boundary kernel" is general (`prop:copy`(b)) and is fine.

## 5. (LD) and M1

**(LD) as stated** (`sec_setting.tex` line 53): `|f(n) - f(n+1)| = O(f(n)/n)` for each sign. This
is the (LR2-O) of 02 and 03. It holds for `f ∝ n^{-alpha-1}`, it is used only in Section 6.4,
and `thm:window` does not use it. The constants convention names `C_LD` as an example, but no
constant `C_LD` is ever introduced (cosmetic).

**Claim card (M1, `thm:first-diff`).** Hypotheses: (RV) and (SPAN) for the minus sign, and (LR)
and (LD) for the plus sign. (LR) implies (RV), which `lem:plus-diff` needs. The start is fresh
with weights `w_+` and `w_-`. Conclusion: uniformly in `1 <= j <= N^{1-eta}`,
`N Delta R_N = N Delta u + Delta C_w + o(1)`, where `C_w = C - 2 alpha_+ mu_+ w_- u` and
`Delta C_w -> c_a`.

**`lem:plus-diff`, checked line by line.**
- (ii): the difference at `n-1` and `n` on `{I = i}` is
  `sum_{z <= n-1-w} h_i(z)[f(n-1-z) - f(n-z)] - h_i(n-w)f(w)`. I derived this by substituting
  `z = n' - y`. (LD) and `eq:f-uct` bound the bracket by `Cf(n)/n`, since `n-1-z >= n/K_0`.
  The second term is at most `C m f(n) f(w) <= C f(n)/n`, because `m f(n) <= C/n`. Summing
  over `i <= m` gives the factor `m`. The truncated part is `n^{-alpha-3} = o(f(n)/n)` by
  `lem:truncated`, with exponent about `K_0/4`.
- (iii): `delta V_m(n) = sum_x f(x)[V_m(n-x) - V_m(n)]`. The part `x <= n/2` is `O(m f(n)/n)`.
  The part `x > n/2` is `f(n)(1+o(1))`, by `P(S_m > eps n) <= m mu/(eps n)`.
- (iv): `q_{m+1}(l-1) - q_{m+1}(l) = V_{m+1}(l-1) - V_m(l-1)` follows from `eq:q-cover`, and
  holds also at `l = 1`, `m = 0`. The two halves each give `mu f(n)`, using
  `sum_y q_{m+1}(y) = mu`, and `T(n)^2 = o(f(n))` holds because `nT(n) -> 0`.
- One cosmetic point: (iii) is applied at arguments `n - i >= n/2`, where the range
  `m <= n^{1-eta}` should be read with `eta/2`. The proof already says this for
  `lem:local-bigjump`.

**`thm:first-diff`, checked line by line.**
- The four-term split follows from `prop:fresh-identity`, with `a_m = u^-_m`,
  `Q_m = q^+_{m+1}` or `q^+_m`, `V_m = u^+_m`, and `b_m = q^-_m` or `q^-_{m+1}`.
- Facts (1) to (6) check:
  - (2): `A-bar_i(j) = sum_{x<j} u_i(x) u(j-x)`, and its difference has absolute sum at most
    `1 + ||d||_1`.
  - (4): `v + u = u*u` follows from `v^ = U^2 - U`, and the difference is `[z^{j+1}] U d^`.
  - (5): `B-bar_i(j) = P(S_i < j)`. Its difference is `u_i(j)`, and the column sum of
    `Delta b` is `0` (plus start) or `f_-(j)` (minus start).
  - (6): the index of the covering run is at most `j`.
- Both summations by parts are correct.
- II and III each give `f_+(N)u(j)` for both starts.
- IV is `O(f_+(N) j/N)`.
- I gives `T_+(N) Delta u + f_+(N)[(j+1)Delta u + 2 mu_+ Delta v - 2 mu_+ w_- Delta u]`.
- With `C(j) = alpha_+[j u + 2 mu_+ v + sum_{i<j} u(i)]` I get
  `Delta C = alpha_+[(j+1)Delta u + 2 mu_+ Delta v + 2u]`, as used.
- The limit is `alpha_+(2 mu_+/mu_-^2 + 2/mu_-) = 2 alpha_+ s/mu_-^2`.

Proved as written.

## Summary of requested changes

1. `thm:ends` proof: add the `eta'/2` step for (d) and for the minimizer clause (section 4).
2. Abstract, last sentence: limit it to fresh or fair starts, or say "for fresh starts" (optional).
3. Note 17, section 3: replace the minus-start example by `f(1) = 0.2`, `f(2) = 0.3` with a
   zeta tail, or drop the numbers (notes only).
4. Cosmetic: `C_LD` in the constants paragraph; read `eta/2` when (iii) of `lem:plus-diff` is
   applied at shifted arguments.

## Fixes made (October 25, 2026)

1. `thm:ends` proof. The end of the proof now applies (b) and (c) with `eta'/2`. With
   `j_L = floor(L) + 1` and `j_U = ceil(U) - 1`, this gives `D_N(j_L) < 0` and `D_N(j_U) > 0`
   for large `N`, hence (d) inside the open window. It also makes `g` strictly decreasing up to
   `j_L + 1` and strictly increasing from `j_U - 1` on, so every minimizer lies in `(L, U)`.
2. Abstract, last sentence. It now reads "For fresh and fair starts with no ties in the kernel,
   under a smoothness condition, ...". To stay under 250 words I tightened four other phrases
   without changing any claim. The abstract is now 247 words.
3. `C_LD`. The constant does exist. It is the local large deviation constant of
   `lem:stable`(iii) in the appendix, so the remark in section 5 above was wrong. Defining a
   second `C_LD` at (LD) would use the name twice. Instead the constants paragraph now says
   that `C_LD` is the constant of `lem:stable`(iii) and is not tied to (LD).
4. `lem:plus-diff`. The first paragraph of the proof now says that (ii) and (iii) are applied at
   arguments `n' >= n/2` with `eta/2` in place of `eta`, since `n^{1-eta} <= (n')^{1-eta/2}`
   for large `n`. `thm:first-diff` already said this for its use of the lemma.

Rebuilt with no undefined or multiply defined references and no overfull boxes. 62 pages.
`py -I verify_all.py --quick` passes.
