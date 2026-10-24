# Paper F audit 05: `sec_bigjump.tex` (big jumps and the boundary layer)

Scope: all of `sec_bigjump.tex`, read against the macros in `problem131_levy.tex`,
the definitions and identities in `sec_setting.tex`, and Theorem `thm:bulk` and
Lemma `lem:stable` (plus (K1) to (K4), `lem:kernels`, `lem:small` and
`lem:index` for notation) in `sec_bulk.tex`. I took Theorem `thm:bulk` as given.
For the consistency question I read only the statements of `thm:preparation`,
`lem:unif-bigjump` and `thm:antimode`, and the sentences where they invoke
`thm:bigjump`. No file in the paper was edited.

Scripts are in `scripts/bigjump/` of this folder
(`giant_check.py`, `mutant.py`, `hratio.py`, `exact_law.py`), all run with `py -I`.

---

## 0. Summary

The section's own proofs hold up. The giant identity is exact (checked
symbolically). The Chernoff lemma is correct with constants that do not depend on
the truncation level. The spread lemma needs only tightness. The one-giant-run
lemma, the two-giant-runs bound and the proofs of (a), (b) and (c) close. The
example is correct, and the numbers 0.31, 1.68 and 1.09 reproduce.

The serious problem is **between sections**. Theorem `thm:bigjump`(b) is stated
on the zone `pN + K lambda_N B_N`. Remark `rem:theta` proves, correctly, that the
zone `pN + K B_N` fails when `theta_{+,N} -> 0`. But `lem:unif-bigjump`(ii) and
`thm:preparation`(c) in `sec_preparation.tex`, and the far-from-layer step of
`thm:antimode` in `sec_shape.tex`, call on (b) over the zone `pN + K B_N`, with no
`lambda_N`. As written, `thm:preparation`(c) and `lem:unif-bigjump`(ii) are false
whenever `theta_{+,N} -> 0` along a subsequence, for example when
`alpha_+ > alpha_-`. The antimode use is repairable, because the lower-bound half
of (b) does hold on `pN + K B_N` (see Section 2.1).

Ranked list:

| # | Severity | Where | Issue |
|---|---|---|---|
| 1 | Major (cross-section) | `sec_preparation` `lem:unif-bigjump`(ii), `thm:preparation`(c); `sec_shape` `thm:antimode` | They use (b) on `pN+KB_N`, but (b) is proved, and by `rem:theta` only true, on `pN+K lambda_N B_N`. |
| 2 | Moderate | `lem:no-big-run` | The statement allows `0<eta<=1/4` (so `r>=1/4`), but the proof uses `r>=4>1/alpha_+`. The lemma needs `r>1/alpha_+`. The application, with `eta<=1/32`, `r>=2`, is fine. |
| 3 | Moderate (claim calibration) | preamble lines 103-106, `rem:theta` | "The factor `lambda_N` is forced" overclaims. What is proved is that some factor tending to infinity is needed. The logarithm is an artifact of the fixed-exponent left-tail bound, and `(1+log(1/theta_+))^{(alpha_- - 1)/alpha_- + delta}` would do. |
| 4 | Minor | `lem:spread` | Index slip: `m_2=floor((i+w)/mu_-)+1` with event `S_{m_2}<i` is wrong. It should be `m_2=floor((i+w)/mu_-)` (then deviation `w-mu_-`, as the text says). Also `epsilon'` should be chosen by picking `Z` for `Z/2`. |
| 5 | Minor | lines 89-94 | The claim that `G_N(N-1)` "matches" `P_N(N-1)=f_+(N-1)` holds only asymptotically: `floor(L_k)=floor(N-s/mu_-)` is not `N-1` in general. It needs (LR) to say `f_+(floor(L_k))/f_+(N-1) -> 1`. |
| 6 | Minor | proof of (a), lines 241-245 | "These are of order `T_+(N)/N` at fixed `j`" needs (LR). Under (RV) alone they are only `o(T_+(N))`, which is all the proof uses. |
| 7 | Minor | `rem:wr` | "the lower bound `G_N(k)>=cT_+(N)` comes from the censored term alone" fails at bounded `j` with `kappa(j)=0` (for example `f_-(1)=0`, `j=1`). There `G_N=gamma(j)f_+`, so a lower bound on `f_+` is still needed for the ratio form. |
| 8 | Editorial | throughout | Constant names clash with `sec_bulk` (`C_4`, `C_5` already name constants of `lem:small`). `thebibliography` is empty, so every `\cite` in the section is undefined. Odd phrasing: "`|I_h|>=m/3`", "`Z/K<=eta/2`". |

---

## 1. Statement-by-statement audit

### 1.1 Lemma `lem:giant` (the giant identity): sound, verified exactly

The proof's split matches the definitions. On `{A_N=k}`:

- a final plus run must start after all `j` minus slots, so its start is
  `t=j+x`, and its probability is `rho_j(x)=A_{j+x}(x)`. So
  `C_lambda` is the first sum of `prop:final-run` restricted to `N-t>=lambda`;
- a complete giant run after the `i`-th minus slot (`i<j` is forced, since the
  next slot is a minus slot) is followed by a fresh minus walk on
  `n=(j-i)+x'` slots holding `j-i` minus slots. That walk has probability
  `beta_{j-i}(x')=K^-_{n}(j-i)`.

Representations (`rho-rep`) and (`beta-rep`) are correct. In particular `X_J` is
independent of `(J, S^+_{J-1}, Y_1..Y_J)`, because `J` is a function of the minus
runs only. The crude bounds (`giant-crude`) follow from (`weight-masses`). The
second mass identity is the Green identity, and summing it gives exactly
`gamma(j)`.

**Exact check.** `giant_check.py` builds `rho_i(x)` from the `A_t` recursion
(`AB-recursion`), checks it against (`rho-rep`), builds `beta_i(x)` by
brute-force enumeration of fresh minus walks, and compares
`E[G_lambda 1{A_N=k}]` and the full split (`giant-split`) with a brute-force
enumeration of all run sequences. The laws are symbolic: `f_+(n)=a_n`,
`f_-(n)=b_n`, and in the "formal" mode `T_+(n)`, `T_-(n)` are independent
symbols, which is a strictly stronger test. Result: **0 mismatches for every
`N<=8`, both starting signs, every `lambda in [1,N]` and every `0<=j<N`**. With
`T=1-sum f` it also gives 0 mismatches (`N<=6`). A mutant in which the `beta`
index is shifted when `i=0` is caught (10 mismatches at `N<=4`), so the test has
power.

### 1.2 Lemma `lem:truncated` (Chernoff for truncated right deviations): sound

Every step checks:

- `e^v<=1+v+v^2e^theta/2` for `0<=v<=theta`, by the Taylor remainder;
- `E[X^2 1{X<w}]=sum_{i<w}(2i-1)P(i<=X<w)<=2 sum_{n<w} nT(n)<=2C_4w^2T(w)`,
  by Karamata (`karamata`) for `nT(n)` in RV of index `1-alpha in (-1,0)`, with
  a constant uniform in `w>=1` because the ratio is positive and convergent;
- `m T(w) e^theta=(mT(w))^{1/2}=e^{-theta}`, so the quadratic term is
  `C_4 theta^2 e^{-theta}<=C_4`, and the bound is `e^{C_4}(mT(w))^{z/(2w)}`.

The constants depend only on the plus law (through `C_4`) and not on `m`, `w` or
`z`. The truncation level enters only through `mT(w)` and the exponent
`z/(2w)`. That is the expected Fuk–Nagaev shape, with exponent `z/(2w)` in place
of the sharp `~z/w`. The factor 2 is the price of `theta` being half the log.
Attributing it to Fuk–Nagaev and to Nagaev 1979, Theorems 1.1 and 1.2, matches
how Caravenna and Doney use Nagaev in their Step 1 (Thm 1.2 for
`alpha in (1,2)`).

### 1.3 Lemma `lem:no-big-run`: sound for `eta<=1/16`; statement needs a fix (gap #2)

The decomposition into `S_1` and `S_2`, and the reduction to four suprema, are
correct. `sum_m q^eta_{m+1}<=sum_m q^+_{m+1}(k)<=1` justifies the
`B`-part of `S_1`.

Set `A` (plus excess). The half-splitting argument is correct: on
`S_m=v'` with `v'-m mu>=L/4`, one half exceeds its mean by `L/8`. Then
`lem:truncated` with `w=eta L`, `z=L/8`, which gives exponent `1/(16 eta)=r`,
times `lem:stable`(ii) for the other half.

The step "the right side is largest up to a constant at `m=M`" needs
`m^r/a_+(m/2)` to be RV with positive index, so `r>1/alpha_+`. The text says
"`r>=4>1/alpha_+`", which holds only for `eta<=1/64`. The statement allows
`eta<=1/4`, that is `r>=1/4`, and for `r<1/alpha_+` the supremum sits at small
`m` and the stated bound fails. **Fix:** state the lemma for `0<eta<=1/16`, so
`r>=1`, or say "`r>1/alpha_+`". Every use takes `eta<=1/32`, so `r>=2`, and is
unaffected.

Set `B` (minus deficit). Correct. `C_0=8c_3 mu_+/mu_-` makes `c_3 b_- <= y_2/4`,
the monotonicity of `t^{-1}e^{-y_2/(4t)}` is used correctly, and the far range
`m>2N/mu_-` gives `e^{-N^c}`. The minus-start index shift is harmless.

The remark after the lemma compares it with Caravenna–Doney Theorem 1.1, (1.4).
That is accurate: (1.4) reads
`P(S_n in x+J, M_n<=gamma x)<=C_0 a_n^{-1}(n/A(x))^{ceil(1/gamma)}` for
`alpha in (0,1) cup (1,2)`, mean zero if `alpha>1` (checked in arXiv:1612.07635v3,
p. 2). In fact (1.4) could replace `lem:truncated` together with the
half-splitting step, with exponent `ceil(1/(4 eta))` in place of `1/(16 eta)`.
The in-house proof is fine.

### 1.4 Lemma `lem:two-big-runs`: sound

The pair formula is correct: three weights, and the complete/final case with
`T_+(L_2)`. The bound `(n-1)^+<=n(n-1)/2` counts unordered pairs. The
convolution bounds are right:
`sum f f<=2f^*(lambda)T(lambda)` and
`sum f T<=f^*(lambda)sum_{n>=lambda}T(n)+T(lambda)^2<=(C_4C_5+1)T(lambda)^2`.
The weight masses are `<=(1+mu_+)(j+1)^2` and `<=j+1`. (LR) enters only through
`f^*(lambda)<=C_5T(lambda)/lambda`.

### 1.5 Lemma `lem:spread`: sound with the index fix (gap #4)

It uses only tightness of `(S_m-m mu)/a(m)`, through `tau_sigma(z)->0`, plus
`a_sigma(m)<=c_5B_N` for `m<=4N/mu_-`. The appeal to `lem:stable`(iv) for
`P(J>3N/mu_-)` could equally use the law of large numbers.

One slip. From `J>(i+w)/mu` one gets `J>m'` with `m'=floor((i+w)/mu)`, hence
`S_{m'}<i`, a deficit of at least `w-mu`. The text takes
`m_2=floor((i+w)/mu)+1` and the event `S_{m_2}<i`. That implication fails when
`J=m_2`. Use `m'` instead; the claimed deviation `w-mu_-` is then exactly right.

The `V_i` bound is correct: the count of `x in [S,S+R]` with `|x-c|>z` is at most
`(1+R)1{|S-c|>z/2}+R1{R>z/2}`, and `R<=X_J` with `X_J` independent of `(J,S)`.

### 1.6 Lemma `lem:one-big-run` (double limit): sound

- **`C_lambda`.** The identity `N-j-x=L-(x-j mu_+/mu_-)` is correct, because
  `N-j-j mu_+/mu_-=N-js/mu_-=L`. On the good `x` the window has relative width
  `<=Z/K+1/L`, so the uniform convergence theorem for `T_+` applies (only (RV)
  is needed), and the indicator is 1 once `Z/K` is small. On the bad `x` the
  weight is `W_j(ZB_N)<=epsilon<=(epsilon/kappa_*)kappa(j)`. `kappa_*>0` by the
  renewal theorem, which needs (SPAN) for the minus sign.
- **`I_lambda`, renewal sum over the start.** `nu_j=sum_{i<j} rho_i * beta_{j-i}`
  has mass `gamma(j)`, by (`weight-masses`). The bad-mass bound
  `sum_i[(1+mu_+)W_i+kappa(i)V_{j-i}]<=(2+mu_+)j epsilon'<=((2+mu_+)/gamma_*)epsilon'gamma(j)`
  is correct. Choose `Z` so that the spread lemma holds at `Z/2` (gap #4,
  cosmetic).
- **Exactly where (LR) enters.** At the line
  "`|f_+(n)/f_+(L^)-1|<=omega_f(Z/K)` for `|n-L^|<=ZB_N+1`". This is where the
  average of `f_+` over the window of width `O(B_N)` carried by `nu_j` is
  replaced by the point value `f_+(floor L_k)`. It is the uniform convergence
  theorem applied to `T_+(n)/n` and `f_+(n)~alpha T_+(n)/n`. (LR) is used a
  second time for `f^*(lambda)<=C_eta f_+(L^)`. `rem:wr` and the paragraph after
  the proof describe this correctly.
- **The coefficient.** `gamma(j)=sum_{i<j}kappa(i)(1+mu_+u_-(j-i))`. Its
  asymptotics come from a Cesàro argument:
  `(1/j)sum kappa(i)->1/mu_-` and `(1/j)sum kappa(i)u_-(j-i)->1/mu_-^2`.
  Together these give `gamma(j)/j -> 1/mu_- + mu_+/mu_-^2 = s/mu_-^2`, and
  `js/mu_-^2=(N-L_k)/mu_-` by (`Lk`). Correct.
- **The censored term with the boundary kernel.** It is correct, and it needs
  no (LR).
- **Order of limits.** For fixed `epsilon`, letting `N` and then `K` go to
  infinity leaves `C epsilon`; then `epsilon -> 0`. That is valid, since the
  left side does not depend on `epsilon`.
- **`lambda_N`.** The lemma holds on `L_k>=KB_N` and does not need `lambda_N`.
  This matters for Section 2.1.

### 1.7 Theorem `thm:bigjump`(a): sound

It needs only (RV) for the plus sign and `mu_+<infinity`: no (LR), no (SPAN).
With `lambda'=ceil((N-j)/(j+1))`, the counting lemma kills the no-giant term. The
last term is `O(T_+(N)^2)`. `I_lambda<=gamma(j)f^*(lambda')=o(T_+(N))` by
(`fstar-small`). The final-minus-run configurations (a complete giant run
followed by a minus run of length `m<=j`) are inside `I_lambda` and are handled
by this crude bound, which is legitimate (gap #6 concerns only the remark that
they are of order `T/N`). `C_lambda` is handled by dominated convergence for
`x<=N/4`. For `x>N/4` it uses (`one-summand`), `rho_j(x)<=j f^*(N/(4j))`, valid
for both starts. `j=0` is exact. The closing remark should also list long-tailedness,
`T(n+1)/T(n) -> 1`, among the uses of (RV). It is implicit in (`fstar-small`) and
in the step "for each fixed `x` the ratio tends to 1".

### 1.8 Theorem `thm:bigjump`(b): sound as stated (on the zone with `lambda_N`)

- **Ratio form, convention `0/0=1`.** For small `j<J_0`, with
  `eta<=1/(2J_0+2)`, the counting lemma gives `P(A_N=k, M_N<eta L)=0`. If
  `G_N=0`, then `C=I=0`, hence `G_lambda=0` a.s. on `{A_N=k}`, hence
  `P_N(k)=0`. So "`G_N=0` only if `P_N=0`" is proved. Otherwise `G_N>=cT/L`,
  and the two-run term over `G_N` is `<=CJ_0^2 L T(L) -> 0`.
- **Large `j>=J_0`.** `G_N>=c_6(N/L)T_+(L)` is correct. The two-run ratio is
  `<=CNT(L)<=CK^{-(alpha_+ +1)/2}`. The no-run ratio has three parts, each
  checked. The first is `(NT)^{r-1}L/b_+<=CK^{(1-alpha_+)/2}`, which needs
  `NT(L)<=1`, true for large `K`. The middle is
  `x^{alpha_+ +2} rho^{alpha_+ +1} e^{-cx}`; I recomputed it from (`NT-bounds`).
  When `rho<=1`, `x>=K`. When `rho>1`, `x>=K(1+log rho)` and
  `rho^{alpha+1}e^{-cx/2}<=e^{-cK/2}` once `cK>=2(alpha_+ +1)`. Correct. This is
  the only place `lambda_N` is used.
- (`NT-bounds`) follows from Potter with `delta=1` for the lower bound and
  `delta<=(alpha-1)/2` for the upper bound, together with
  `NT(b_{+,N}) -> s`. Correct.
- **Additive form.** `G_N<=C_7 Ĝ_N`, because `gamma(j)<=(1+mu_+)j` and
  `f_+(L^)<=2C_5T(L^)/L`. Correct.
- **Replacing `gamma` by `(N-L_k)/mu_-`.** The change is
  `<=2C_5|gamma(j)-js/mu_-^2| T(L^)/L`. For `j>=J_eps` this is
  `<=2C_5 eps Ĝ_N`. For `j<J_eps` it is `<=2C_5C_eps Ĝ_N/N`, because
  `T(L^)/L=Ĝ_N/N`. **The claim holds** in the additive form, not in the ratio
  form; the text before the theorem explains why the ratio form fails at
  bounded `j` with `kappa(j)=0`, which is correct apart from gap #5.

### 1.9 Theorem `thm:bigjump`(c): sound

Bins with `j<=delta_N N` lie in every `K`-zone for large `N`, because
`lambda_N B_N=O(log N) N^{(1+1/alpha_*)/2}=o(N)`. The double limit then
collapses to a single limit, by the standard "for every `K`" argument. The
rest checks:

- `T(L^)/T(N) -> 1` uniformly;
- `gamma f_+(L^)/(kappa T(N))<=C(j+1)/(kappa_* N) -> 0`;
- `Ĝ_N<=4T(N)`.

Both the absolute and the ratio forms follow.

### 1.10 `lambda_N` and Remark `rem:theta` (gap #3)

**What is proved.** The remark is correct: if `theta_{+,N} -> 0` along a
subsequence, then at `k=ceil(pN+KB_N)` with `K` fixed, `B_N P_N(k)` is bounded
below by `thm:bulk`(c), while `B_N G_N(k)<=(C/K)NT(L_k)+B_NT(B_N) -> 0`. So the
old zone fails, in ratio form and also in the additive form, since
`B_N Ĝ_N(k)<=(1/K)NT(L_k) -> 0`. Hence any valid zone start
`pN+omega_N B_N` must have `omega_N -> infinity` along such subsequences.

**What is not proved.** That `omega_N` must be as large as `log(1/theta_+)`. The
preamble sentence "The factor `lambda_N` is forced too" overclaims. The
remark's own last sentence ("a smaller factor should suffice") is right, and
here is why. The logarithm comes only from `lem:stable`(iv), whose exponent is
frozen at `theta=1`. Optimizing the exponent fixes this. Since
`e^y(1-y)<=1`,
`E e^{-s(X-mu)}<=1+e^{s mu}Phi(s)`, and for `s=theta/a(m)<=1` Potter gives
`m log E e^{-theta(X-mu)/a(m)}<=C theta^{alpha+delta}` for
`1<=theta<=a(m)`. Hence
`P(S_m<=m mu-y)<=C exp(-c (y/a(m))^{beta})` with
`beta=(alpha_-+delta)/(alpha_-+delta-1)>1`. The second term of
`lem:no-big-run` becomes `(C/b_-) exp(-c (L/b_-)^beta)`. The middle part of the
proof of (b) is then `x^{alpha+2} rho^{alpha+1} exp(-c x^beta)`, which is small
once `x>=K(1+log rho)^{1/beta}`. So
`lambda_N=(1+log(1/theta_{+,N}))^{1/beta}` for any
`1/beta>(alpha_- - 1)/alpha_-` suffices: **the logarithm is an artifact.** The
true threshold is plausibly `(log(1/theta_+))^{(alpha_- - 1)/alpha_-}`, matching
the left tail `exp(-c|x|^{alpha_-/(alpha_- - 1)})` of `Z_-`. Proving that it is
necessary would need a lower bound on bins in the moderate-deviation range of
the bulk, which `thm:bulk` (additive `o(1)`) cannot give. Suggested rewording:
"some factor tending to infinity is necessary (Remark rem:theta); the
logarithm is what our left-tail bound gives."

### 1.11 Corollary `cor:infinite-density`: sound

Recomputed: `j~(1-p)(1-ell)N`, `gamma(j)~(1-ell)N/mu_-`,
`f_+(L^)~alpha ell^{-alpha-1}T(N)/N`, `T(L^)~ell^{-alpha}T(N)`,
`kappa -> 1/mu_-`. The sum is `I_+(v)`. It is not integrable at `p`, from
either term. Only (LR) for the plus sign is needed. The claim about Vezzani,
Barkai and Burioni ("whose rigorous derivation they leave open") was not
checked: the source is not cited in a form I could locate, and the bibliography
is empty.

### 1.12 Example `ex:rv-not-lr`: sound

- **(RV).** `T(n)~cn^{-alpha}` since `h -> 0`, and `T(1)=1`.
- **(SPAN).** `T` is strictly decreasing (across a block end,
  `(n_i+1)^{-alpha}(1+h_{i+1})<n_i^{-alpha}(1+h_i)`), so `f>0` everywhere.
- **(LR) fails.** At the block ends,
  `f(n_i)=c[(n_i^{-alpha}-(n_i+1)^{-alpha})(1+h_{i+1})+n_i^{-alpha}h_i/2]`, so
  `n_i f(n_i)/T(n_i)~n_ih_i/2 -> infinity`.
- **`P/G -> 0` at `N_i=2n_i`, `k_i=3n_i/2`.** `L_k=n_i` is an integer and
  `gamma(j)~n_i/mu`, so `G>=(c/4mu)h_in_i^{1-alpha}`. For the upper bound,
  `lem:no-big-run` with `eta=1/32`, `r=2` gives `Cn_i^{2-2alpha}`;
  `C_lambda<=Cn_i^{-alpha}`; and
  `I_lambda<=Cn_i^{-alpha}+Ch_in_i^{-alpha}sup nu_j`. The last needs
  `sup nu_j=o(j)`, and the argument is correct: `sup(rho * beta)<=min(...)`,
  one index is `>=j/2`, and `sup rho_n`, `sup beta_n -> 0` by the law of large
  numbers and `lem:stable`(ii). The facts `n_{i-1}=sqrt n_i<n_i/32` and
  `n_{i+1}=n_i^2>2n_i` isolate the single spike. Every comparison
  (`n^{2-2alpha}`, `n^{-alpha}`, both `=o(h n^{1-alpha})`) holds because
  `h_i^{-1}=log n_i`.
- **Addition worth stating.** The additive form of (b) also fails here, since
  `G/Ĝ~h_in_i/(4 mu) -> infinity`.

**Citation.** DDS Theorem 9.1 (arXiv:math/0703265v3, p. 39) assumes the
hypotheses of their Proposition 9.1 and that `x -> F(x+Delta)` is intermediate
regularly varying, and concludes `P(S_n in x+Delta)~nF(x+Delta)` uniformly for
`x>=x_n`. The paper's description ("assume that `x -> P(X in x+Delta)` is
intermediate regularly varying, which is a local hypothesis") is accurate.

### 1.13 Remark `rem:no-single-formula`: sound; numbers reproduced

The leading term `B_N G_N(k) -> alpha_+(1-p)^{alpha_+}K^{-alpha_+-1}` is
recomputed and correct. It is the leading tail of `h_N`, since
`P(Z_+>x)~x^{-alpha}` with this normalization: `hratio.py` checks
`g(x)/(alpha x^{-alpha-1})=0.99934` at 50 and `0.99999` at 200.

For equal laws with `alpha=1.5`, `p=1/2`, `theta=1`, Fourier inversion
(`mpmath`, 30 digits) gives:

| K | h(K) | h(K)/lead |
|---|---|---|
| 1 | 0.165791 | **0.3126** |
| 2 | 0.104437 | 1.114 |
| 4 | 0.027799 | **1.6774** |
| 8 | 0.003765 | 1.285 |
| 16 | 0.000566 | **1.0934** |
| 32 | 9.45e-5 | 1.032 |
| 64 | 1.64e-5 | 1.011 |

So 0.31, 1.68 and 1.09 are correct.

I also checked the claim "exact laws at `N=1200` and `3000` approach these
values", for the zeta law `f(n)=n^{-2.5}/zeta(2.5)` (the law named in
`sec_verify`), computing the exact row by the recursion of `prop:final-run`
(mass `1+3e-14`):

| K | P/G at N=1200 | P/G at N=3000 | limit |
|---|---|---|---|
| 1 | 0.354 | 0.337 | 0.313 |
| 4 | 1.482 | 1.538 | 1.677 |
| 16 | 1.036 | 1.059 | 1.093 |

Both move monotonically toward the limits, so "approach" is fair. At `N=3000`
they are still 7–8% off at `K=1` and `K=4`. Wording such as "move toward" would
be safer. At `K=16`, `L_k` is a large fraction of `N`, so the approximation
`j~(1-p)N` behind the leading term is still poor at these `N`
(`B_NG_N/lead=0.77` and `0.83`). The limit claim `P/(h/B_N+G) ->` (a value
below 1) is trivially correct.

### 1.14 Remark `rem:wr`: mostly right, one gap (gap #7)

The list of the three uses of (LR) is accurate. The argument that window
regularity at relative width `Z/K -> 0` together with (RV) implies (LR) is
sound: `T(n)-T((1+delta)n)` evaluated two ways. The ballistic-range claim needs
a caveat. When `kappa(j)=0` at bounded `j`, `G_N=gamma(j)f_+(L^)` has no censored
term. Window regularity plus `f=O(T/n)` does not bound `f_+(L^)` below, and the
two-run error `CJ_0^2T(L)^2` must be `o(f_+(L^))`. Either assume
`f_-(1)>0` (then `kappa(j)>0` for every `j>=1`) or state only the additive
form there.

---

## 2. Consistency with `sec_preparation.tex` and `sec_shape.tex`

### 2.1 `thm:antimode` (sec_shape, proof of (`anti-far`)): inconsistent but repairable

The proof says: "By Theorem `thm:bigjump`(b) there is `K` such that
`P_N(k)>=(1-eps)G^{(+)}_N(k)` for `pN+KB_N<=k<=N`". It then covers
`pN<=k<pN+KB_N` by `thm:bulk`(c). (b) gives this only for
`k>=pN+K lambda_N B_N`. When `theta_{+,N} -> 0`, which `thm:antimode` allows,
the bins in `[pN+KB_N, pN+K lambda_N B_N)` are covered by neither.

**Repair (I checked it).** The lower bound holds on the larger zone. By
(`giant-split`) and positivity of the no-giant term,
`P_N(k)>=C_lambda+I_lambda-E[(G_lambda-1)^+1{A_N=k}]`.
`lem:one-big-run` needs only `L_k>=KB_N`. The two-run ratio is
`<=CNT_+(L)<=C(L/b_+)^{-(alpha_+ +1)/2}<=CK^{-(alpha_+ +1)/2}`, using only
`L>=KB_N>=Kb_{+,N}`. In the small-`j` case it is `<=CJ_0^2LT(L)`. So:

> (b′) Under the hypotheses of (b),
> `lim_K liminf_N inf_{pN+KB_N<=k<=N, G_N(k)>0} P_N(k)/G_N(k) >= 1`.

Adding (b′) to `thm:bigjump` and citing it in `thm:antimode` closes the gap.
Only the upper bound needs `lambda_N`.

### 2.2 `lem:unif-bigjump`(ii) and `thm:preparation`(c): inconsistent, and false as stated

- `lem:unif-bigjump`(ii) claims `|F_n-G_n|<=eps Ĝ_n` for
  `pn+K_0B_n<=k<=n`, citing `thm:bigjump`(b).
- `thm:preparation`(c) is stated on `pN+KB_N<=k<=N`.

Take a fresh plus start as the preparation. When `theta_{+,N} -> 0` along a
subsequence, the argument of `rem:theta` gives `B_NP_N(k)>=c` while
`B_N(G_N+Ĝ_N)(k) -> 0` at `k=ceil(pN+KB_N)`, for every fixed `K`. So both
statements are false in that regime, for instance whenever
`alpha_+>alpha_-`. (Under the bulk theorem the extra preparation terms only add
nonnegative mass, so this does not rescue them.)

**Repair.** Put `lambda_n` into both zones. For the delay steps (Step 1 of the
decomposition) this is harmless: for `N/2<=n<=N`, Potter gives
`lambda_n<=lambda_N+C<=(1+C)lambda_N`, so `K` is replaced by `K/(1+C)`. But the
`Psi_N` window estimate (the `|i|>R` blocks, lines ~530-545) chooses `R` so that
`y>=K_0B_m` at both ends. With `lambda` it needs `R` of order
`K_0 lambda_N`, which can grow like `log N`. The bound
`(2R+2)C_eps^2 bar W_N` on the near blocks then has to be rechecked. The minus
end uses the minus-end `lambda` (with `theta_-`). I did not audit that section.
I flag it as **the remaining gap for `thm:preparation`(c)**, not as a settled
error in its proof.

`sec_inverse.tex` uses only (a) and is consistent.

---

## 3. Citations checked

- **Caravenna–Doney, arXiv:1612.07635v3, Thm 1.1 and (1.4).** Verified verbatim
  (p. 2). Hypothesis (1.2) with `p>0`, mean zero for `alpha>1`, and the norming
  `a_n=A^{-1}(n)`. The section's use (the analogy for `lem:no-big-run`) is
  accurate. Their Step 1 attributes the non-local bound to Nagaev 1979,
  Thms 1.1 (`alpha<1`) and 1.2 (`alpha in (1,2)`). The section's attribution of
  `lem:truncated` is consistent with that.
- **Denisov–Dieker–Shneer, arXiv:math/0703265v3, Thm 9.1.** Verified (p. 39).
  It is the intermediate-regular-variation local hypothesis, as the section
  says.
- **BGT 1.5.2, 1.5.6, 1.5.8 and 1.5.10.** Used in the standard way.
- **Nagaev 1979.** Not checked against the original. As used (attribution only),
  it agrees with how Caravenna–Doney cite it.
- **Rebenshtok et al. and Vezzani–Barkai–Burioni.** Not checked.
- **Bibliography.** `thebibliography` in `problem131_levy.tex` is empty, so
  every key in this section is currently undefined: `bgt1989`, `fuknagaev1971`,
  `nagaev1979`, `caravennadoney2019`, `dds2008`, `rdhb2014`, `rdhb2014b`,
  `vbb2019`.

---

## 4. Verdicts

| Statement | Verdict | Remaining gap |
|---|---|---|
| `lem:giant` | Sound (verified exactly, `N<=8`, symbolic) | none |
| `lem:truncated` | Sound | none |
| `lem:no-big-run` | Sound with listed fix | restrict to `eta<=1/16` (or `r>1/alpha_+`); fix "`r>=4`" |
| `lem:two-big-runs` | Sound | none |
| `lem:spread` | Sound with listed fix | `m_2 -> floor((i+w)/mu_-)`; choose `Z` for `Z/2` |
| `lem:one-big-run` | Sound | none; it holds on `L_k>=KB_N` with no `lambda_N` |
| `thm:bigjump`(a) | Sound (needs only (RV)+ and `mu_+<infinity`) | none |
| `thm:bigjump`(b), ratio, additive, and with `(N-L_k)/mu_-` | Sound as stated | none in this section; add (b′) for downstream use |
| `thm:bigjump`(c) | Sound | none |
| `rem:theta` | Sound as a proof that the old zone fails | the "forced" wording overclaims; the log is not necessary as shown |
| `cor:infinite-density` | Sound | external claim about VBB unchecked |
| `ex:rv-not-lr` | Sound | none (it also violates the additive form) |
| `rem:no-single-formula` | Sound; numbers reproduced | soften "approach" (7–8% off at `N=3000`) |
| `rem:wr` | Sound with listed fix | `kappa(j)=0` caveat on the ballistic range |
| Text at lines 89-98 | Sound with listed fix | "matches" is asymptotic under (LR) |
| Consistency: `thm:antimode` | Inconsistent, repairable | needs (b′) on `pN+KB_N` (proved above) |
| Consistency: `lem:unif-bigjump`(ii), `thm:preparation`(c) | Inconsistent; false as stated when `theta_{+,N} -> 0` | add `lambda_n` to the zones and recheck the `Psi_N` block estimate with `R ~ K_0 lambda_N` |
