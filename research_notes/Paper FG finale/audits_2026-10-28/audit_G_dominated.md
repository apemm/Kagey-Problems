# Audit of Theorem `thm:dominated` and Lemma `lem:R` (Paper G, `sec_dominated.tex`)

Date: 2026-10-28. Scope: `kagey-problems/problem131/paperG/sec_dominated.tex`, read against
`sec_setting.tex`, `sec_tools.tex`, `sec_appendix.tex` (`lem:rv-facts`) and Paper F's
`lem:stable` (Lemma A.1). The cited lemmas `lem:cd`, `lem:sums`, `lem:key`, `lem:decay`,
`lem:onejump`, `lem:Q` are taken as given with their stated hypotheses. No file in `paperG` or
`paperF` was edited. The numeric checks quoted below were run from a scratch script
(`lam_check.py`, scratchpad only).

Verdict vocabulary: **proved as written** / **correct only after a stated restriction** /
**conditional on a named input** / **incomplete** (smallest missing implication named) /
**refuted** (counterexample).

Standing fact used repeatedly, which the section asserts but does not prove and which is
true: under (DOM) with `alpha_- < 1`, `T_-(D_N) ~ T_+(N)` by the definition of `a_-`; if
`D_N >= cN` along a subsequence then `T_-(D_N) <= T_-(cN) <= C_c T_-(N) = o(T_+(N))`, a
contradiction. So `D_N = o(N)` in that case without any index comparison. The same argument
gives `a_+(1/T_-(j))/j -> infinity` for every `j -> infinity` (since
`T_+(a_+(1/T_-(j))) ~ T_-(j) = o(T_+(j))`), which repairs two of the gaps below.

The recurring source of trouble is the case `alpha_+ = alpha_-` with `T_-/T_+ -> 0` through
slowly varying factors. (DOM) allows it, and the section's own opening paragraph discusses
`alpha_+ = alpha_- = alpha`, `b = 0`. In that case `D_N` has index exactly `1`, `D_n/n` is
slowly varying (tending to `0`), and several "negative index" or "positive index" sentences
in the proofs are false even though most conclusions survive.

---

## 1. Opening paragraphs

### 1.1 Claim: `D_N` nondecreasing, regularly varying with positive index below 1, `D_N = o(N)`

Claim card. Case `mu_- < infinity`: `D_N = mu_-/T_+(N)`, index `alpha_+ in (0,1)`. Case
`alpha_- < 1`: `D_N = a_-(1/T_+(N))`, index `alpha_+/alpha_-`.

Derivation. Nondecreasing: `T_+` nonincreasing, `a_-` increasing. `D_N = o(N)`: finite-mean
case by `N T_+(N) -> infinity`; infinite-mean case by the standing fact above (not by the index,
which is `1` when `alpha_+ = alpha_-`).

Verdict: **correct only after a stated restriction.** `D_N = o(N)` and monotonicity are
proved for every pair allowed by (DOM). The phrase "regularly varying in `N` with a positive
index below 1" is false when `alpha_+ = alpha_- < 1`: `D_N = a_-(1/T_+(N))` then has index
`alpha_+/alpha_- = 1` (`D_N = N L(N)` with `L -> 0` slowly varying). Example:
`T_+(x) = x^{-1/2}`, `T_-(x) = x^{-1/2}/log x`, giving `D_N ~ N/(log N)^2` up to constants.
Consequence: the sentence "`D_n/n` is regularly varying with a negative index" used in the
(W_+) paragraph is false in that case; see 2.6 and 2.8.

### 1.2 Claim: `Psi(0+) = 1` in both cases

Derivation (infinite-mean case). Density of `E_+^{1/alpha_-} Z_-` at `y` is
`int_0^infinity phi(x) x^{-1/alpha_-} g_-(y x^{-1/alpha_-}) dx`. With `v = y x^{-1/alpha_-}`,
`x = (y/v)^{alpha_-}`, `dx = -alpha_- y^{alpha_-} v^{-alpha_- - 1} dv`, this is
`alpha_- y^{alpha_- - 1} int_0^infinity phi((y/v)^{alpha_-}) g_-(v) v^{-alpha_-} dv`, matching the
text. `phi` is bounded and continuous with `phi(0+) = 1` (from `phi(x) = g(x^{-1/alpha}) x^{-1/alpha-1}/alpha`
and `g(w) ~ alpha w^{-1-alpha}`), and `v^{-alpha_-} g_-(v)` is integrable (superexponential decay
of `g_-` at 0, tail `v^{-1-alpha_-}` at infinity), so dominated convergence applies.
`E Z_-^{-alpha_-} = (1/Gamma(alpha)) int lambda^{alpha-1} e^{-Gamma(1-alpha) lambda^alpha} d lambda
= 1/(alpha Gamma(alpha) Gamma(1-alpha)) = sin(pi alpha)/(pi alpha)`; numerically `0.50455` for
`alpha = 0.6` both ways. Hence `rho(y) ~ (sin pi alpha_-/pi) y^{alpha_- - 1}` and `Psi(0+) = 1`.
Finite-mean case: `Psi = phi`, `phi(0) = 1` as recorded in `sec_tools`.

Verdict: **proved as written.**

### 1.3 Claim: for `alpha_+ = alpha_- = alpha`, `b = 0`, the limit is `Z_-/Z_+` with density (eq:ratio-density), "which is also the limit of `b^{-1/alpha} La(1 - b^{1/alpha} y)` as `b -> 0`"

Derivation. `E_+ = Z_+^{-alpha}`, so `E_+^{1/alpha} Z_- = Z_-/Z_+`. Mellin check: for the
standard positive stable law `E Z^s = Gamma(1 - s/alpha)/Gamma(1 - s)`, so
`E (Z_-/Z_+)^s = sin(pi s)/(alpha sin(pi s/alpha))`. The displayed density, after
`x = y^alpha`, becomes `(sin pi alpha/(pi alpha)) /(1 + 2x cos pi alpha + x^2)`, whose Mellin
transform `int x^{s-1}/(1 + 2x cos theta + x^2) dx = (pi/sin pi s) sin((1-s) theta)/sin theta`
reproduces the same moments. Numerically: the density integrates to `1.00000` and
`E R^{1/4}` agrees with the formula to the grid error (`1.2187` vs `1.2201`). So
(eq:ratio-density) is correct.

The Lamperti limit. From `La(1-y) = (sin pi alpha/(pi b)) y^{alpha-1} Phi_b(y)` (checked against
eq:L-cosh), with `y = b^{1/alpha} y'`:
`La(1 - b^{1/alpha} y') = (sin pi alpha/pi) b^{-1/alpha} y'^{alpha-1} Phi_b(b^{1/alpha} y')`, and
`Phi_b(b^{1/alpha} y') -> 1/(1 + 2 y'^alpha cos pi alpha + y'^{2 alpha})`. Therefore
`b^{+1/alpha} La(1 - b^{1/alpha} y') ->` the ratio density, while
`b^{-1/alpha} La(1 - b^{1/alpha} y') ~ b^{-2/alpha} x (ratio density) -> infinity`. This is also
the only scaling consistent with the setting: under (BAL) with small `b`,
`a_-(t) = a_+(bt) ~ b^{1/alpha} a_+(t)`, so `D_N ~ b^{1/alpha} N`, and `(N - A_N)/D_N` has
density `b^{1/alpha} La(1 - b^{1/alpha} y)`. Numeric check at `alpha = 0.6`, `y in {0.3, 1, 2.5}`:
`b^{1/alpha} La(1 - b^{1/alpha} y)` equals the ratio density to 4 digits at `b = 10^{-4}`,
and `b^{-1/alpha} La(...)` is of order `10^{13}`.

Verdict: **ratio density proved as written; the Lamperti-limit sentence is refuted as
written** (the prefactor must be `b^{1/alpha}`, not `b^{-1/alpha}`). The continuity statement
"the balanced and the dominated regime join continuously at `b = 0`" is true with the corrected
prefactor.

### 1.4 Claim: (W_+) for one `delta` is (W_+) for every `delta`

Derivation. For `delta < delta'`, the extra terms are `m in (delta/T_+(n), delta'/T_+(n)]`,
at most `delta'/T_+(n)` of them, each `<= C/a_+(m) <= C/a_+(delta/T_+(n))` by `lem:cd`(i) and
monotonicity of `a_+`. `a_+(1/T_+(n))/n -> 1` (`lem:rv-facts`(iii) with `t = 1`), and
`a_+(delta t)/a_+(t) -> delta^{1/alpha_+}` for fixed `delta`, so `a_+(delta/T_+(n)) >= c_delta n`.
The difference of the two left sides is `<= C_delta D_n/n -> 0` (by 1.1, in every case including
`alpha_+ = alpha_-`). The converse direction is monotone.

Verdict: **proved as written.**

---

## 2. Lemma `lem:R`

### 2.1 `lem:R`(i), `mu_- < infinity`

Claim card. `lim_{A} limsup_{j} sum_{|m - j/mu_-| > A a_-(j)} u^-_m(j) = 0` under (RV), (SPAN) for
the minus sign.

Derivation. Paper F Lemma A.1(ii) gives `u^-_m(j) = a_-(m)^{-1}[g_-((j - m mu)/a_-(m)) + o(1)]`
uniformly in `j` as `m -> infinity`; on the window `m -> infinity` with `j`, and
`a_-(m) ~ mu^{-1/alpha_-} a_-(j)` uniformly there because `a_-(j) = o(j)`. In
`z = (j - m mu)/a_-(m)` the step is `mu/a_-(m)(1 + o(1))`, so the window sum is a Riemann sum
converging to `mu^{-1} int_{|z| <= A mu^{1 + 1/alpha_-}} g_-(z) dz`; the error terms contribute
`o(1) A a_-(j)/a_-(m) = o_A(1)`. With `u_-(j) -> 1/mu_-` (renewal theorem, needs (SPAN) and finite
mean) the complement is `mu^{-1} int_{|z| > c A} g_- + o(1) -> 0` as `A -> infinity`.

Check of the written text. The integration range is written `|z| <= A/mu_-`; the correct range
is `|z| <= A mu_-^{1 + 1/alpha_-}`. This changes nothing in the limit.

Verdict: **proved as written** (cosmetic error in the stated range of the limiting integral).

### 2.2 `lem:R`(ii), `alpha_- < 1`

Claim card. `sum_{m > K/T_-(j)} u^-_m(j) <= C K^{1 - 1/alpha_-}/(j T_-(j))` for all `K >= 1`,
`j >= 1`, with one constant `C`.

Independent derivation. With `t = 1/T_-(j)`, `lem:sums`(iii) gives
`u^-_m(j) <= C a_-(m)^{-1} e^{-m T_-(j+1)/3} <= C a_-(m)^{-1} e^{-m/(6t)}` for `j >= j_0`.
Summing over dyadic blocks `m in (2^l K t, 2^{l+1} K t]` and using Potter's lower bound
`a_-(2^l K t) >= c (2^l K)^{1/alpha_- - eps} a_-(t)` (valid uniformly in the ratio `>= 1` for
`t >= t_0`) gives a total `<= C K^{1 - 1/alpha_- + eps} e^{-K/6} t/a_-(t) <= C K^{1 - 1/alpha_-}/(j T_-(j))`,
since `K^eps e^{-K/6}` is bounded and `a_-(1/T_-(j)) >= c j`. Small `j` is a finite set and the sum
is `0` once `K t > j`. So the statement is true.

Check of the written proof. It bounds `u^-_m(j) <= C/a_-(m)`, sums to `C M/a_-(M)` with
`M = K/T_-(j)`, and then asserts `a_-(M) >= c K^{1/alpha_-} j` "by (R2) for `a_-`". (R2) is a
fixed-ratio comparison with a constant depending on the ratio; it does not give a bound uniform
in `K`. The inequality `a_-(K t) >= c K^{1/alpha_-} a_-(t)` with `c` independent of `K >= 1` and
`t` is false in general: for `a(t) = t^{1/alpha} exp(-sqrt(log t))` (increasing for large `t`,
regularly varying with index `1/alpha`, a legitimate scale for an aperiodic law with
`T = 1/a^{-1}`), `a(Kt)/(K^{1/alpha} a(t)) = exp(sqrt(log t) - sqrt(log t + log K)) -> 0` as
`K -> infinity` for every fixed `t`, and equals `0.046` already at `K = t = 10^{24}`. For that
scale the quantity the proof actually bounds, `C M/a_-(M)`, exceeds the claimed bound by the
unbounded factor `L(t)/L(Kt)`.

Use in the section. Both uses (`sec:dom-bulk` large range, and the (d) main term) take `K`
fixed and `j -> infinity`; for fixed `K`, `a_-(K/T_-(j)) ~ K^{1/alpha_-} j`, so the written
argument does deliver the bound for `j >= j_0(K)`, which is all that those uses need.

Verdict: **incomplete.** Smallest missing implication: the uniform-in-`K` lower bound
`a_-(K/T_-(j)) >= c K^{1/alpha_-} j` does not follow from (R2) and fails for some scales. The
statement is nonetheless true; the repair is `lem:sums`(iii) plus Potter's bound with exponent
`1/alpha_- - eps`, as above. Alternatively, weaken the statement to `limsup_j` for fixed `K`,
which is what the section uses.

---

## 3. Theorem `thm:dominated`

### 3.1 (a) The global law

Claim card. `(N - A_N)/D_N` converges in law to `rho`, under (DOM) and (SPAN), fresh start of
either sign.

Check. From (b), summing `P_N(N - j)` over `j in [y_1 D_N, y_2 D_N]` is a Riemann sum with mesh
`1/D_N`, so `liminf P((N - A_N)/D_N in [y_1, y_2]) >= int_{y_1}^{y_2} rho`. `rho` is a
probability density on `(0, infinity)` (law of `E_+` or of `E_+^{1/alpha_-} Z_-`). A subsequential
limit measure dominates `rho dx` on every compact of `(0, infinity)` and has total mass `<= 1`,
hence equals `rho dx`: convergence in law. (b) is unconditional, so (a) is too.

Verdict: **proved as written.**

### 3.2 (b) The lower half

Check. All terms of the fresh identity are nonnegative. The middle range of `I_N(j)` alone
gives `D_N I_N(j) >= int_eps^K phi(x) x^{-1/alpha_-} g_-(y x^{-1/alpha_-}) dx - o(1)` uniformly in
`y in [y_1, y_2]` (the Riemann-sum step is checked in 3.3), and the integral increases to
`rho(y)` uniformly on `[y_1, y_2]` as `eps -> 0`, `K -> infinity` (the tail near `0` is
`O(eps^2 y_1^{-1-alpha_-})`, the tail beyond `K` is controlled by the superexponential decay of
`g_-` at `0`). In the finite-mean case (b) is implied by (c), which is unconditional there.

Verdict: **proved as written.**

### 3.3 (c) Sufficiency

Claim card. If `mu_- < infinity` or `alpha_- > 1/2`: uniform local law on
`[y_1 D_N, y_2 D_N]` with no further condition. If `alpha_- <= 1/2`: under (SRT_-) and (W_+).

Main term, `mu_- < infinity`. On the window `|m - j/mu_-| <= A a_-(j)`,
`m T_+(n) = j T_+(n)/mu_- + O(A a_-(j) T_+(N)) = y(1 + o(1)) + o(1)` since `a_-(j)/j -> 0` and
`D_N T_+(N) = mu_-`; so `m T_+(n) <= y_2 + 1 =: K` and `lem:Q`(ii) applies with `k = n`;
`phi` is uniformly continuous on `[0, K]`; `lem:R`(i) gives window mass `1/mu_- - o_A(1)`;
`lem:key` bounds the off-window kernel by `C T_+(N)`. All `o(1)` are uniform in `y`. Correct.

Main term, `alpha_- < 1`. `T_-(j) ~ y^{-alpha_-} T_+(N)` uniformly by (R1) and
`T_-(D_N) ~ T_+(N)`. Middle range: `lem:cd`(i) is uniform as `m >= eps/T_+(N) -> infinity`;
`lem:Q`(ii) at `k = n` with `m T_+(n) <= K + 1`; `a_-(x/T_+(N)) ~ x^{1/alpha_-} D_N` uniformly on
`[eps, K]` by (R1) for `a_-`. The sum in `x = m T_+(N)` with mesh `T_+(N)` is
`(1/D_N) sum Delta x x^{-1/alpha_-} g_-(y x^{-1/alpha_-}) phi(x) (1 + o(1))`, and the integrand is
uniformly continuous on `[eps, K] x [y_1, y_2]`. Error terms: `o(1) T_+(N) (K/T_+(N))/a_-(eps/T_+(N)) = o(1/D_N)`.
Riemann sum re-derived and correct, uniform in `y`. Large range: `lem:key` plus `lem:R`(ii) with
`K' = K T_-(j)/T_+(N) ~ K y^{-alpha_-}` (fixed `K`, so the lemma's proof suffices here),
`j T_-(j) ~ y^{1 - alpha_-} D_N T_+(N)`; bound `C_{y_1,y_2} K^{1 - 1/alpha_-}/D_N`. Correct. Small
range: `eps/T_+(N) = eps'/T_-(j)` with `eps' <= C_{y_1} eps`; `I_-` nondecreasing in its first
argument, so the bound is uniform; `lem:cd`(iv) gives `limsup_j I_-(eps', j) -> 0` as `eps' -> 0`
under (SRT_-). Correct.

Second term, `alpha_- < 1`. `lem:key` for the minus sign (`alpha_- < 1`): `q^-_m(j) <= C T_-(j) <= C T_+(N)`.
`m > delta/T_+(n)`: `u^+_m(n) <= C/a_+(delta/T_+(n)) <= C_delta/N`, `sum_m q^-_m(j) = 1`, so
`O(1/N) = o(1/D_N)` by `D_N = o(N)`. `m <= delta/T_+(n)`: `<= C T_+(N) sum_{m <= delta/T_+(n)} u^+_m(n)`,
which is `o(1/D_N)` under (W_+) at `n in [N - y_2 D_N, N - y_1 D_N]` (all `-> infinity`), with
`D_n ~ D_N` by (R1) for `D`. Correct.

Second term, `mu_- < infinity` (the direct count). `m > delta j`: `a_+(delta j) >= c N` because
`j asymp D_N = mu_-/T_+(N)`; `O(1/N) = o(T_+(N))`. `m <= delta j`, `delta mu_- <= 1/4`: for
`r >= j/2`, `r - (m-1) mu_- >= j/4 >= 1`, so Paper F Lemma A.1(iii) applies with
`T_-(r - (m-1) mu_-) <= T_-(j/4) <= C T_-(j)`; `sum_{i >= 1} T_-(i) = mu_-`; hence
`q^-_m(j) <= C T_-(j)(1 + m/a_-(m))`. With `lem:cd`(ii) for the plus sign the part is
`<= C T_+(N) T_-(j) sum_{m <= delta j} (m/a_+(m))(1 + m/a_-(m))`. Partial sums: `m/a_+(m)` has
index `1 - 1/alpha_+ in (-infinity, 0)`, so `sum_{m <= delta j} <= C lambda(j) max(1, j^2/a_+(j))`
(Karamata; `lambda` slowly varying, needed only at `alpha_+ = 1/2`); `m^2/(a_+(m) a_-(m))` has
index `2 - 1/alpha_+ - 1/alpha_-`, partial sums `<= C lambda(j) max(1, j^3/(a_+(j) a_-(j)))`.
Indices of the two products with `T_-(j)`: `-alpha_- + max(0, 2 - 1/alpha_+) < -alpha_- + 1 < 0`
since `alpha_+ < 1 < alpha_-`; and `-alpha_- + max(0, 3 - 1/alpha_+ - 1/alpha_-)`, where
`3 - 1/alpha_+ - 1/alpha_- - alpha_- < 2 - alpha_- - 1/alpha_- = -(sqrt(alpha_-) - 1/sqrt(alpha_-))^2 <= 0`.
Both negative; a slowly varying `lambda` does not change this. So the `m <= delta j` part is
`o(T_+(N))` as `j -> infinity` with no condition on `j/D_N`. Count re-derived and correct. (The
phrase "with no condition on `j/D_N`" applies to the `m <= delta j` part; the `m > delta j` part as
written uses `j asymp D_N`, and `sec:dom-ends` re-does it for `j << D_N` with `lem:cd`(ii), which
is correct.)

Fresh minus start. Kernels `q^+_m`, `q^-_{m+1}`: `lem:Q`(ii) with `m - 1`, `lem:key`, `lem:decay`,
the direct count with `u^-_m` in place of `u^-_{m-1}` (same inequality `r - m mu_- >= j/4` for
`m <= delta j`). No bound or limit changes. Correct.

`alpha_- > 1/2`. (SRT_-) by `lem:cd`(iii). (W_+): see 3.5; it holds for `alpha_- > 1/2` in
every subcase, including `alpha_+ = alpha_- > 1/2` (there `lambda = 1` and `D_n/n -> 0` by the
standing fact, though not with a negative index as written).

Verdict: **proved as written** (for `alpha_- > 1/2` the (W_+) input is proved only after the
correction recorded in 3.5, which costs nothing).

### 3.4 (c) Necessity for `alpha_- <= 1/2`

Failure of (SRT_-). `lem:cd`(iv) and monotonicity of `I_-(delta, x)` in `delta` give `c > 0`
such that for every `eps' > 0`, `I_-(eps', j) >= c` along a sequence `j -> infinity` (depending
on `eps'`). Order of choices, checked: fix `y in (y_1, y_2)`, fix `K` and `eps'` with
`eta(eps', K) < c'/4` and `eps' <= delta_0 y_1^{alpha_-}/2` (so that `m < eps'/T_-(j)` implies
`m T_+(n) <= delta_0` and `lem:Q`(i) gives `q^+_{m+1}(n) >= T_+(N)/2 (1 + o(1))`); fix `eta` with
`|rho(y') - rho(y)| < c'/4` for `|y' - y| <= eta` (`rho` is continuous); then take the sequence
of `j` and choose `N` with `j/D_N in [y - eta, y + eta]`, which exists since `D_N` is
nondecreasing with `D_{N+1}/D_N -> 1` (regular variation of `a_-` and of `1/T_+`). Small range
`>= (c/2) T_+(N)/(j T_-(j)) (1 + o(1)) >= c'/D_N` with `c' = c y_2^{alpha_- - 1}/4`, independent
of `eps'`, since `j T_-(j) ~ (j/D_N)^{1 - alpha_-} D_N T_+(N)`. Middle range
`>= (rho(j/D_N) - eta(eps', K) - o(1))/D_N`, with the middle range starting at
`eps'/T_-(j)`, i.e. at `x = eps' (j/D_N)^{alpha_-}` (consistent relabeling of `eps`). Dropping the
nonnegative rest, `D_N P_N(N - j) - rho(j/D_N) >= c' - c'/4 - o(1) >= c'/4` along the sequence.
Correct.

Failure of (W_+). By 1.4 the failure holds for every `delta`, so one may take `delta` with
`m T_-(j) <= delta_0` for `m <= delta/T_+(n)` and `j >= y_1 D_N` (this is the constraint that
matters, since `T_-(j)` is largest at the small end of the window; the text writes
`j <= y_2 D_N`, a slip without consequence). `lem:Q`(i) for the minus sign (`alpha_- < 1`)
gives `q^-_m(j) >= T_-(j)/2`, so `R_N(j) >= (1/2) T_-(j) sum_{m <= delta/T_+(n)} u^+_m(n) >= c T_-(j)/(2 D_n T_+(n)) >= c''/D_N`,
with `T_-(j)/T_+(n) ~ (j/D_N)^{-alpha_-}` and `D_{n+j} ~ D_n` since `j = o(n)`. Given `n`,
`j -> j/D_{n+j}` moves in steps `~ 1/D_n -> 0`, so a `j` with `j/D_N` near `y` exists. The
proof of (b) gives `D_N I_N(j) >= rho(j/D_N) - o(1)` without (W_+), hence
`D_N P_N(N - j) >= rho(j/D_N) + c'' - o(1)`. Correct.

Verdict: **proved as written** (one harmless slip, `j <= y_2 D_N` should read `j >= y_1 D_N`).

### 3.5 (c) Last sentence: (W_+) holds under (SRT_+), and whenever `alpha_+ >= 1/2` or `alpha_- > 1/2`

Under (SRT_+): `sum_m u^+_m(n) = u_+(n) <= C/(n T_+(n))`, left side `<= C D_n/n -> 0` (1.1).
Correct in both cases of `mu_-`.

`alpha_+ < 1/2`: `sum_m m/a_+(m)` converges (index `< -1`), left side
`<= C D_n T_+(n)^2`. For `alpha_- < 1` this is `~ C D_n T_-(D_n)^2 -> 0` iff `alpha_- > 1/2`
(index `1 - 2 alpha_-`). For `mu_- < infinity` the identity `T_+(n) ~ T_-(D_n)` is not available
but `D_n T_+(n)^2 = mu_- T_+(n) -> 0` directly; the written paragraph is scoped to `alpha_- < 1`,
so this is a scope remark, not an error.

`alpha_+ >= 1/2`: partial sums `<= C lambda(M) M^2/a_+(M)` with `lambda = 1` for
`alpha_+ > 1/2` (Karamata, index `> -1`) and `lambda` slowly varying, possibly unbounded, at
`alpha_+ = 1/2` (index exactly `-1`). With `M = delta/T_+(n)` and `a_+(M) >= c_delta n`, the sum
is `<= C_delta lambda(1/T_+(n))/(n T_+(n))` (re-derived: the prefactor `T_+(n)` from `lem:cd`(ii)
cancels one of the two powers), and the left side is `<= C_delta lambda(1/T_+(n)) D_n/n`. The
text concludes with "`D_n/n` is regularly varying with a negative index". Case check:
- `alpha_+ < alpha_-` (any `alpha_+ >= 1/2`): index `alpha_+/alpha_- - 1 < 0`, slowly varying
  times negative index `-> 0`. Correct.
- `alpha_+ = alpha_- > 1/2`: `lambda = 1` and `D_n/n -> 0` by the standing fact. Conclusion
  correct, reason as written false (index is `0`).
- `alpha_+ = alpha_- = 1/2`: `lambda(1/T_+(n))` may be unbounded and `D_n/n` is slowly varying;
  the bound `lambda(1/T_+(n)) D_n/n` need not tend to `0`. Explicit instance of the bound
  failing: `T_+(x) = x^{-1/2}`, `a_+(m) = m^2`, `lambda(M) ~ log M`,
  `T_-(x) = x^{-1/2} (log x)^{-1/4}`, giving `D_n/n asymp (log n)^{-1/2}` and
  `lambda(1/T_+(n)) D_n/n asymp (log n)^{1/2} -> infinity`. This refutes the proof's bound, not
  (W_+) itself; whether (W_+) can fail for some plus law with `alpha_+ = 1/2` whose (SRT_+)
  failure is strong enough to beat a slowly varying `D_n/n` is not settled here, and the paper
  itself records that the question is open for `alpha_+ < 1/2`.

Verdict: **incomplete.** Smallest missing implication: (W_+) at `alpha_+ = alpha_- = 1/2`
(with `T_-/T_+ -> 0` through slowly varying factors and (SRT_+) not assumed). Everything else in
the sentence is proved, after replacing "negative index" by "`D_n/n -> 0`" for
`alpha_+ = alpha_- > 1/2`. The theorem's sufficiency claim for `alpha_- > 1/2` is unaffected.
A minimal honest restatement would read "whenever `alpha_- > 1/2`, or `alpha_+ >= 1/2` with
`alpha_- > 1/2`"; the remaining line `alpha_+ = alpha_- = 1/2` then falls under the
if-and-only-if of (c) as a hypothesis.

### 3.6 (d) Fixed `j` (and fixed `i`)

Check. `u^-_m(j) = 0` for `m > j`. For fixed `m`,
`q^+_{m+1}(n) = P(S^+_{m+1} >= n) - P(S^+_m >= n)` (the event `{S_m < n <= S_{m+1}}` is the set
difference since `S_m <= S_{m+1}`), and `P(S_m >= n) ~ m T_+(n)` for fixed `m` under (RV)
(subexponentiality; `lem:onejump` also covers it with `m T(y) <= eps` eventually), so
`q^+_{m+1}(n) ~ T_+(n) ~ T_+(N)`. Hence `I_N(j) ~ T_+(N) sum_{m=1}^j u^-_m(j) = T_+(N) u_-(j)` for
`j >= 1`, and `P_N(N) = T_+(N) = T_+(N) u_-(0)` for the fresh plus start. `R_N(j)`: only
`m <= j` occur (the text says `m <= j+1`, harmless). `u^+_1(n) = f_+(n) = T_+(n) - T_+(n+1) = o(T_+(n))`
under (RV); for `m >= 2` some summand is `>= n/m`, so
`u^+_m(n) <= m sup_{x >= n/m} f_+(x) = o(T_+(n/m)) = o(T_+(n))`. So `R_N(j) = o(T_+(N))`. Only (RV)
for the plus sign is used; the minus side enters through the finite numbers `u^-_m(j)`. Fresh
minus start: `P_N(N) = F^-_N(N) = 0 = u_-(0) 1_{0 >= 1}`, and for `j >= 1` the main term is
`sum_{m >= 1} u^-_m(j) q^+_m(n) ~ T_+(N) u_-(j)`. The minus end is the mirror, and the
subexponentiality step holds for `alpha_- in (1,2)` as well (regularly varying tails of any
index are subexponential), so (RV) for the minus sign alone suffices.

Verdict: **proved as written.**

### 3.7 (d) The uniform matching on `0 <= j <= y_2 D_N`, `alpha_- != 1/2`, and the fallback at `alpha_- = 1/2`

Claim card. Under the condition of (c) and `alpha_- != 1/2`:
`P_N(N - j) = T_+(N)[kappa(j) Psi(j/D_N) + o(omega(j))]` uniformly over `0 <= j <= y_2 D_N`. At
`alpha_- = 1/2`, the same under (SRT_+) with `alpha_+ < 1/2`.

Range `1 << j << D_N`, main term. Finite mean: window mass at `m ~ j/mu_-`, and
`m T_+(N) <= j/D_N + A a_-(j) T_+(N) -> 0`; `lem:Q`(ii) with `phi(0+) = 1` gives
`q^+_{m+1}(n) = T_+(N)(1 + o(1))` on the window; `lem:key` off it. Infinite mean: mass beyond
`K/T_-(j)` is `<= C K^{1 - 1/alpha_-}/(j T_-(j)) <= C K^{1 - 1/alpha_-} u_-(j)` by `lem:R`(ii)
(fixed `K`) and the lower half of (SRT_-); on `m <= K/T_-(j)`, `m T_+(N) <= K T_+(N)/T_-(j) -> 0`
because `j/D_N -> 0` forces `T_-(j)/T_-(D_N) -> infinity` (Potter), and `T_-(D_N) ~ T_+(N)`. Both
re-derived; `I_N(j) = T_+(N) u_-(j)(1 + o(1))` along every sequence `j -> infinity`,
`j/D_N -> 0`. Correct.

Range `1 << j << D_N`, second term, `alpha_- < 1`. Ratios re-derived against
`T_+(N) omega(j) = T_+(N)/(j T_-(j))`:
- `m > delta/T_+(n)`: part `<= C_delta/N`, ratio `<= C j T_-(j)/(N T_+(N)) <= C D_N T_-(D_N)/(N T_+(N)) ~ C D_N/N -> 0`
  (Potter for `sup_{j <= D_N} j T_-(j)`). Correct.
- `m <= delta/T_+(n)`, `alpha_+ >= 1/2`: `sum_m (m/a_+(m)) e^{-c m T_-(j)} <= C lambda(M) M^2/a_+(M)`
  at `M = 1/T_-(j)` (dyadic blocks beyond `M` are killed by the exponential; checked), ratio
  `= C lambda(1/T_-(j)) j/a_+(1/T_-(j))`. The text then says this tends to `0` because
  `a_+(1/T_-(j))/j` has positive index `alpha_-/alpha_+ - 1` "when `alpha_+ < alpha_-`, and
  `alpha_+ >= 1/2` with `alpha_- != 1/2` forces `alpha_+ < alpha_-`". The quoted implication is
  false: `alpha_+ = alpha_- = alpha in (1/2, 1)` with `T_- = o(T_+)` is allowed by (DOM) (for
  instance `T_+(x) = x^{-0.7}`, `T_-(x) = x^{-0.7}/log x`). In that case the index is `0`.
  The conclusion still holds: `lambda = 1` because `alpha_+ > 1/2`, and
  `j/a_+(1/T_-(j)) -> 0` by the standing fact (`T_+(a_+(1/T_-(j))) ~ T_-(j) = o(T_+(j))`). At
  `alpha_+ = 1/2 < alpha_-` the written reason is right (`lambda` slowly varying times a
  negative-index factor).
- `alpha_+ < 1/2`, `alpha_- > 1/2`: ratio `<= C j T_-(j)^2 -> 0`, index `1 - 2 alpha_- < 0`. Correct.
- `alpha_+ < 1/2`, `alpha_- < 1/2`: by (W_+) at `n`, ratio `<= o(1) j T_-(j)^2/(D_N T_-(D_N)^2) <= o(1)`,
  since `x T_-(x)^2` has positive index and `j <= D_N` (BGT 1.5.3 for the sup). Correct.
- `alpha_- = 1/2`: the `alpha_+ >= 1/2` route leaves `lambda(1/T_-(j)) j/a_+(1/T_-(j))`, where
  the second factor does tend to `0` (standing fact) but `lambda` may be unbounded; the
  `alpha_+ < 1/2` routes leave `l_-(j)^2` or `l_-(j)^2/l_-(D_N)^2`, slowly varying and not
  necessarily bounded. The exclusion is a non-claim and is consistent. Fallback: under (SRT_+)
  with `alpha_+ < 1/2`, the part is `<= C T_-(j) u_+(n) <= C T_-(j)/(n T_+(n))`, ratio
  `C j T_-(j)^2/(N T_+(N)^2) = C l_-(j)^2/(N T_+(N)^2)`, and `l_-(j) <= C N^eps` for `j <= N`
  while `N T_+(N)^2` has index `1 - 2 alpha_+ > 0`. The main term at `alpha_- = 1/2` needs
  (SRT_-), which is part of "the condition of (c)" there. Correct.

Range `1 << j << D_N`, second term, `mu_- < infinity`. `m > delta j`:
`<= C T_+(N) sup_{m > delta j} m/a_+(m) <= C_delta T_+(N) j/a_+(j) = o(T_+(N))`; `m <= delta j`:
the count of 3.3, which is free of `j/D_N`. Correct, and `omega = 1`.

The matching. On `1 << j << D_N`: `Psi(j/D_N) -> 1` (1.2 and continuity of `Psi`), `kappa_+(j) = u_-(j)`
for `j >= 1`, and `u_- <= C omega` ((SRT_-), or boundedness of `u_-` in the finite-mean case)
turns `o(u_-(j))` into `o(omega(j))`. On `j asymp D_N`: with (SRT_-) and
`j T_-(j) ~ y^{1 - alpha_-} D_N T_+(N)`, `T_+(N) u_-(j) Psi(y) = (sin pi alpha_-/pi) y^{alpha_- - 1} Psi(y)/D_N (1 + o(1)) = rho(y)(1 + o(1))/D_N`,
and `T_+(N) omega(j) asymp 1/D_N`; finite mean: `u_-(j) -> 1/mu_-`, `T_+(N)/mu_- = 1/D_N`,
`Psi = phi`. So (c) is exactly the claim there. Bounded `j`: 3.6 with `Psi(j/D_N) -> 1` and
`omega(j) >= c`. The subsequence argument (any sequence `j_N` has a subsequence that is bounded,
or `-> infinity` with `j_N/D_N -> 0`, or with `j_N/D_N -> y > 0`) is valid because each range
statement was proved along arbitrary such sequences. At `j = 0` the formula reads `Psi(0)`,
which needs the convention `Psi(0) = Psi(0+) = 1`.

Verdict: **incomplete, with a one-line repair.** Smallest missing implication: in the case
`alpha_+ = alpha_- in (1/2, 1)` the sentence "`alpha_+ >= 1/2` with `alpha_- != 1/2` forces
`alpha_+ < alpha_-`" is false; what is needed and true is `j/a_+(1/T_-(j)) -> 0`, which follows
from `T_- = o(T_+)` and (R2) (standing fact). With that sentence replaced, (d) is proved as
stated, including the exclusion of `alpha_- = 1/2` and the fallback under (SRT_+), `alpha_+ < 1/2`.

---

## 4. Applications of the cited lemmas, hypothesis check

- `lem:cd`(i),(ii),(iv): used for the sign with index in `(0,1)` only; for the minus sign only
  when `alpha_- < 1`. Finite-mean minus sums use Paper F Lemma A.1(ii),(iii) instead, within
  their hypotheses (`r - (m-1) mu_- >= 1`). In order.
- `lem:cd`(iii): used for `alpha_- > 1/2`. In order.
- `lem:key`, `lem:decay`, `lem:Q`: plus sign always (`alpha_+ < 1`), minus sign only when
  `alpha_- < 1` (second term, necessity, (d)). In order.
- `lem:sums`: not invoked directly in this section; it is what repairs `lem:R`(ii).
- `lem:onejump`: fixed-`m` subexponentiality, `m T(y) <= eps` eventually. In order.
- Regular variation with slowly varying factors: the three places where the text asserts a
  strict sign of an index that is in fact `0` when `alpha_+ = alpha_-` are 1.1, 3.5 and 3.7. Two
  of the three conclusions survive by the standing fact; the third (3.5 at
  `alpha_+ = alpha_- = 1/2`) does not follow from the written bound.

## 5. Summary of verdicts

| Claim | Verdict |
|---|---|
| `D_N` nondecreasing, `D_N = o(N)` | proved |
| `D_N` RV with positive index below 1 | refuted at `alpha_+ = alpha_-` (index is 1); harmless except as input to 3.5, 3.7 |
| `Psi(0+) = 1`, both cases | proved |
| Ratio density (eq:ratio-density) | proved |
| "limit of `b^{-1/alpha} La(1 - b^{1/alpha} y)`" | refuted as written; correct with `b^{+1/alpha}` |
| (W_+) independent of `delta` | proved |
| `lem:R`(i) | proved (integration range misprinted) |
| `lem:R`(ii) | incomplete as written; statement true via `lem:sums`(iii) + Potter; uses need only fixed `K` |
| (a) | proved |
| (b) | proved |
| (c) sufficiency | proved |
| (c) necessity, both failures | proved (slip `j <= y_2 D_N` for `j >= y_1 D_N`) |
| (c) last sentence on (W_+) | incomplete at `alpha_+ = alpha_- = 1/2`; otherwise proved after replacing "negative index" by `D_n/n -> 0` |
| (d) fixed `j`, fixed `i` | proved |
| (d) uniform matching, exclusion and fallback at `alpha_- = 1/2` | incomplete by one false sentence (`alpha_+ = alpha_- > 1/2`); repaired by `j/a_+(1/T_-(j)) -> 0` from `T_- = o(T_+)` |
