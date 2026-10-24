# Audit of route T2: the Bessel boundary layer between a face and a facet (Theorem 2)

Date: October 24, 2026. Base checkpoint `6add913`. This is a read-only audit. No manuscript file or
research note was edited.

Audited: `research_notes/C theorems 5 and 7/08_T2_boundary_layer.md`, all of it, with its scripts
`08_layer_core.py`, `08_layer_check.py`, `08_layer_check2.py`, `08_layer_check3.py`,
`08_prefactor_check.py` and their outputs, and the notation of `00_targets.md`. I checked it against
the printed material it uses: `paperC/sec_model.tex` (Lemma `lem:runs`, Lemma `lem:continuum`),
`paperC/sec_secondorder.tex` (Definition `def:tilt`, Proposition `prop:constant`, Theorem
`thm:local`, Lemma `lem:discrete`), `paperC/app_torus.tex` (Lemma `lem:perron`, Lemma `lem:torus`,
the proof of the local law with its paragraphs on hypotheses (i) to (iii), regularity and the
constant), `paperC/app_laplace.tex` (Lemma `lem:laplace` and its proof), `paperC/sec_vertex.tex`
(Lemma `lem:uniform-laguerre-bessel`, Theorem `thm:vertex-uniform-root`), `paperC/app_vertex.tex`
(the proof of the Laguerre to Bessel lemma, Lemma `lem:vertex-randomization`) and
`eq:refresh-polynomial` in `sec_complete.tex`.

Scripts written for this audit (all run with `py -I`) are in `scripts/boundary_layer_T2/` of this
folder. Their outputs are quoted below, so this report does not depend on them.

- `a1_lemma1.py`: Lemma 1, formula (2.1), as an identity of power series with symbolic rates and
  start (`d = 3` up to total degree 4, `d = 4` up to total degree 2). Lemma 1' in exact rational
  arithmetic against brute-force path enumeration (`d = 3`, `N = 6, 7`; `d = 4`, `N = 6`).
- `a2_prop3.py`: Proposition 3(i) (the Legendre identity) by direct optimization; `ab`, `j_2`,
  `gamma` against Richardson-extrapolated finite differences of `J`. The chains are the
  non-reversible 3-cycle of the note and a non-reversible 4-state chain (so `g = 3`).
- `a3_layer.py`, `a4_growth.py`: the closed Bessel form of `Phi(z)(s)` for `|G| = 2` at complex
  `z` against the word series. Also the exact continuum density (contour (2.2), mpmath) divided by
  `f_G` times the Bessel kernel, for the non-reversible cycle at `x = delta T`, `T` up to 3200.
- `a5_vertex.py`: Section 8. The pair-face case of Lemma 1' against the draft's representation
  `S_(b,a)(u) = (1 - u)^a E[B_a(v X)]`, symbolically.

## 0. Verdict in one paragraph

The exact part of the note is right. Lemma 1 and Lemma 1' are correct, and I recomputed them
independently. So are Proposition 2 (pair faces), Proposition 3 (Legendre identity, the
coefficients `ab` and `gamma`, the reversible simplifications) and Proposition 4 (reversible
prefactor matching). Sections 6.2 and 6.3 deduce Theorem 2 from Lemma L, and that deduction is
complete for 2(a) and for the reversible half of 2(b). There is one real error. **The general
(non-reversible) error bound of Theorem 2(b), `|E| <= C(1/T + sqrt(x/T)(1 + x))` uniformly on
`0 < x <= delta T`, is false for `x >> T^{1/3}`**. The true relative error grows like
`exp(c x^{3/2} T^{-1/2})`, and at `x = delta T` that is exponential in `T`. I confirmed this
numerically: at `delta = 0.05`, `T = 3200` the ratio is `48268`, while the claimed bound is `36`.
The proof in 6.3 linearizes `exp(O(x^{3/2} S^{-1/2}))`. The note's own Section 6.3 and Part F say
that the Bessel form is good only for `x << T^{1/3}`, so the theorem statement contradicts the
note's own text. The same overclaim sits in 2(c). The fix is one line: restrict to `x <= C T^{1/3}`,
or state the error in logarithmic form (Section 4.1). Lemma L is still the named input for
`|G| >= 3`. I find no obstruction to the route described. For `|G| = 2`, that is `|F| = 3`, the
note missed a short complete proof: the facet density is a closed combination of `I_0` and `I_1`
of a complex argument (Section 5.3). So Theorem 2(a) and 2(b) (corrected) are unconditional for
every three-state face. Theorem 2(c) needs two missing inputs, not one.

## 1. Lemma 1 and Lemma 1' (the exact representation)

**Statement checked.** `M(z) = Q_G + z c^- (c^+)^T`, start `pi(z) = mu_G + z mu_i c^+`, end
`e(z) = 1 + z c^-`, `A(z)` the off-diagonal part, `d(z) = q_G - z c^- o c^+`, and

    e^{q_i x} f_F(s, x) = sum_{K>=1} x^{K-1}/(K-1)! [z^K] Phi(z)(s) = (1/2 pi i) oint e^{x/z} Phi(z)(s) z^{-2} dz.

**Proof by hand.** I went through the bijection. Deleting the isolated letters `i` from a word `c`
in `F` gives a marked word `c'` in `G`. There is at most one mark between unequal letters and
exactly one between equal letters, and the first and last letters can carry an end mark. A mark
between `j, j'` carries `q_ji q_ij'`. The start mark carries `mu_i c^+_{j'}` and the end mark
`c^-_j`. The time factor of `i` is `x^{K-1}/(K-1)!`, and the factors for the states of `G` count
the runs of `c`. Those are the letters of `c'`, not of the reduced word `w`. Collapsing the equal
blocks with the identity `sum_n binom(n + rho - 1, rho - 1) y^n s^{rho+n-1}/(rho+n-1)! =
e^{ys} s^{rho-1}/(rho-1)!` is correct, and it produces exactly the diagonal shift in `d(z)`. The
grouping is a bijection. A word `c` with no letter `i`, or one whose `c'` misses a state of `G`, is
excluded on both sides. The bound `W_z(m) <= k^M (q_max(1 + |z| q_max))^{M-1}` makes `Phi(.)(s)`
entire, and integrating term by term on the circle is legitimate.

**Recomputation.** `a1_lemma1.py`: the difference between `H_F(s, x)` and the right side of (2.1)
(the exponential factors `e^{-<q_G, s>}` cancel) is the zero polynomial up to total degree 4 for a
three-state chain with all six rates and three start masses symbolic. It is also zero up to degree
2 for a four-state chain (`g = 3`, again fully symbolic).

**Lemma 1'.** The block deletion is correct. Each gap between consecutive letters of the reduced
path carries at most one maximal `i`-block, the start and end gaps included. A block of length
`len` contributes `h q_ji (1 - h q_i)^{len-1} h q_ij'`. Pulling out
`prod (1 - h q_i)^{len - 1} = (1 - h q_i)^{n_i - K}` and counting the compositions of `n_i` into `K`
parts gives the formula. `a1_lemma1.py`, in exact rationals with random rates and `h = 1/40`:
10, 15 and 10 compositions with full support (`d = 3, N = 6`; `d = 3, N = 7`; `d = 4, N = 6`), no
mismatch.

**A useful addition the note does not make.** Lemma 1' also has a contour form. With
`sum_K binom(n-1, K-1) y^K = y (1 + y)^{n-1}`,

    P_N(n) = (1/2 pi i) oint P^{(z)}_{N'}(nhat) z^{-2} (1 - h q_i + 1/z)^{n_i - 1} dz,

and after `w = h z` the lattice kernel is `h w^{-2} (1 - h q_i + h/w)^{n_i - 1}`, which is the
discrete form of `e^{-q_i x + x/w} w^{-2}`. This is the formula that 2(c) needs (Section 4.3).

**Verdict.** Proved as written.

## 2. Proposition 3 (the facet expansion of the rate)

**(i) Legendre identity.** The `epsilon = u_i` terms are `-epsilon sum_j s_j c^-_j/u_j -
(x/epsilon) c^+ . u_G`, the optimum over `epsilon` is `-2 sqrt(x S P_beta(u))`, then
`2 sqrt(xSP) = inf_z [S z P + x/z]`, and two suprema always commute. Correct. Numerically
(`a2_prop3.py`), for the 3-cycle and the 4-state chain at `(S, x) = (10, 0.5)` and `(20, 3)`, the two
sides agree to 10 digits (for example `7.3546246597` both ways).

**(ii) Coefficients.** The Hessian of `Psi_beta` in `psi = log u` is `-L_beta`, with conductances
`kappa_jk = l_j q_jk r_k + l_k q_kj r_j`. I rederived this from the sum of
`w e^{psi_k - psi_j} (e_k - e_j)(e_k - e_j)^T`. The envelope theorem gives `J' = -P`, and
`J'' = grad P^T L^+ grad P` comes from `-L psi'(0) = grad P`. Also `grad P = ab (pi^out - pi^in)`.
All correct. Since `J(beta, .)` is a supremum of affine functions of `z`, it is convex, which gives
`j_2 >= 0` independently. Check: for the cycle, `J(z) = 3 - 2z - sqrt((2 + z)(1 + 4z))` exactly at
`beta = (1/2, 1/2)` (the closed two-state rate). It gives `ab = 5.181981`, `J''(0) = 4.331029`,
`gamma - q_3 = 0.417893`, which are the note's values. Richardson extrapolation of the second
differences gives `4.3013, 4.3230 -> 4.3310` for the cycle and `1.6657, 1.6697 -> 1.6711` for the
4-state chain (formula `1.671120`). The note's own finite difference `2.151` against `2 j_2/2 =
2.1655` was a truncation effect, as it says.

**Effective resistance.** `(p - q)^T L^+ (p - q)` with `p - q` of zero sum is the effective
resistance between the laws `p` and `q` in the network `kappa`, and it vanishes exactly when
`p = q`, because the kernel of `L` is the constants. Correct.

**(iii) Expansion.** The two-step localization (first `psi* - psi_0 = O((x/S)^{1/4})`, then the
quadratic expansion) is standard. I checked the coefficient: maximizing
`-(1/2) d^T L d - 2 eps grad p . d` gives `2 eps^2 grad p^T L^+ grad p`, and with
`grad p = grad P/(2 sqrt(ab))` this is `x j_2/ab`. The remainder `O(S eps^3) = O(x^{3/2} S^{-1/2})`
is right. One reference is weak: "the bounded set of the proof of Proposition 3.1(b)" is cited, not
restated. It is a minor point. The concavity of the objective in `psi` and the coercivity of
`Psi_beta` on the complement of the constants (which `G` irreducible gives) suffice and take two
lines.

**(iv) Reversible.** `M(z)` is reversible for `nu_G` for every `z`, and that holds for complex `z`
too, since `nu_j c^-_j c^+_k = nu_i q_ij q_ik`. So `r_beta = sqrt(beta/nu)` does not depend on `z`,
`J(beta, z) = I_G(beta) - z ab` exactly, and `ab = (sum_j sqrt(w_ij beta_j))^2`. I checked the last
identity by hand (`a = sqrt(nu_i) Sigma`, `b = nu_i^{-1/2} Sigma`). Correct. It agrees with
Proposition 3.1(c) of the draft.

**Verdict.** Proved as written. The cross-reference in (iii) should be replaced by the two-line
coercivity argument.

## 3. Proposition 2 (pair faces) and Proposition 4 (reversible prefactors)

**Proposition 2.** With `G = {j}`, `Phi(z)(s) = (mu_j + z mu_i q_ij)(1 + z q_ji) e^{-(q_j - zw)s}`.
That holds since the only word is `j`, and `e(z)` and `pi(z)` are as stated. With (6.1),
`n = 0, 1, 2` give `z_*^{-1} I_1`, `I_0`, `z_* I_1`, and the three coefficients
`mu_j`, `mu_i q_ij + mu_j q_ji`, `mu_i w` reproduce the displayed formula. The two-sided bound
follows from the Amos lower bound `I_1/I_0 >= Z/(1 + sqrt(1 + Z^2))`, which is the case `nu = 0` of
`I_{nu+1}/I_nu >= Z/(nu + 1 + sqrt(Z^2 + (nu+1)^2))`. Then `z_*(1 + 2/Z) = sqrt(x/(ws)) + 1/(ws)`.
This is Pedler's two-state density written as a layer. All correct.

Two small remarks. The bound is valid for all `x, s > 0` as stated. But the sentence "Theorem 2(a)
and 2(b) hold with no restriction on `x`" is true for 2(a) (with `E = 0`) and false for the `O`-form
of 2(b), since `x/s` and `1/(ws)` blow up as `s -> 0`. The note itself says `x <= T/2` one line
earlier. The sentence should say "with the explicit bound, for all `x`". Also `mu_j > 0` is used to
divide.

**Proposition 4.** I redid the computation. On `G`, `r_alpha` and `l_alpha` are `sqrt(1 - e)` times
`r_beta` and `l_beta`. At `i` they are `O(sqrt e)`. So `(mu . r)(l . 1) = (1 - e)(mu_G . r_beta)
(l_beta . 1)(1 + O(sqrt e))`, which needs `mu(G) > 0`. Next, `prod alpha = e (1 - e)^g prod beta`,
and the trees with one edge at `i` give `tree(c(alpha)) = sqrt(e) sqrt(ab) tree(c_G(beta))
(1 + O(sqrt e))`. The ratio is `(4 pi)^{-1/2} (ab)^{1/4} e^{-3/4}`. Converting to occupation
coordinates, `T^{-g/2} S^{(g-1)/2} C_F/C_G` against the large-`Z` Bessel kernel
`(4 pi)^{-1/2} (ab S)^{1/4} x^{-3/4} e^Z`, gives the same powers. So the matching statement is
consistent. The script `08_prefactor_check.py` shows the `sqrt(10)` per decade convergence.

The amplitude derivative `c_1` for reversible `Q` (start term, end term, Kirchhoff term with
`d c_jk/dz = ab pi_j pi_k`) is also right. It uses that the conductances of `M(z)` are
`l_j A(z)_jk r_k` with `r` fixed.

**Verdicts.** Proposition 2: proved as written, with the wording fix about "no restriction".
Proposition 4: proved as written.

## 4. Theorem 2 from Lemma L (Sections 6.2 to 6.4)

### 4.1 Severity 1: the non-reversible error in 2(b) and 2(c) is wrong for `x >> T^{1/3}`

The claim is `|E| <= C(1/T + sqrt(x/T)(1 + x))` uniformly for `0 < x <= delta T`. Section 6.3, case
`1 <= x <= delta T`, correctly derives

    Lamb(rho_s) - Z = -(j_2/ab) x + c_1 z_* + O(x^{3/2} S^{-1/2} + x/S),

and then writes the ratio as `e^{-(gamma - q_i)x}(1 + O(sqrt(x/T)(1 + x)))`. That step replaces
`exp(O(x^{3/2} S^{-1/2}))` by `1 + O(x^{3/2} S^{-1/2})`, which is valid only while
`x^{3/2} S^{-1/2}` is bounded, that is for `x <= C T^{1/3}`. At `x = delta T` the cubic term
`S j_3 z_*^3` is of order `delta^{3/2} T`. So `E` is of order `exp(c delta^{3/2} T)` when the
cubic coefficient has the bad sign, which no `C(1/T + sqrt(x/T)(1 + x))` can bound.

Numerical confirmation (`a3_layer.py`, `a4_growth.py`). Take the non-reversible cycle, uniform
start, `beta = (1/2, 1/2)`, with the exact continuum density from (2.2) and the one-term kernel with
the correct `gamma = 3.417893`. Here `j_3 = J'''(0)/6 = -4.872`, so `e^{-S J}` carries
`e^{+4.87 S z^3}` and the ratio grows.

| delta | T | x | f_F/(f_G B) | claimed bound sqrt(x/T)(1+x) | ratio |E|/bound |
|---|---|---|---|---|---|
| 0.05 | 200 | 10 | 2.79 | 2.46 | 0.73 |
| 0.05 | 800 | 40 | 19.6 | 9.17 | 2.0 |
| 0.05 | 1600 | 80 | 265 | 18.1 | 14.6 |
| 0.05 | 3200 | 160 | 48268 | 36.0 | 1340 |
| 0.02 | 3200 | 64 | 20.0 | 9.19 | 2.07 |

So the inequality fails for every fixed `delta > 0` once `T` is large. The note's Part F data
(`230` at `T = 160`, `45312` at `T = 320`, `x = T/4`) already shows this, and Section 6.3 says
"the non-reversible Bessel form is useful only for `x << T^{1/3}`". The theorem statement, the
summary in Section 0 and Section 9 item (6) need to be brought into line.

**Correct statements**, both supported by the computations already in 6.3:

- (b-rel) for `0 < x <= C_1 T^{1/3}`: `|E| <= C(1/T + sqrt(x/T)(1 + x))`;
- (b-log) for `0 < x <= delta T`: `f_F = f_G B_beta e^{E'}` with
  `|E'| <= C(1/T + sqrt(x/T)(1 + x))`.

For (b-log), every factor in the 6.3 ratio other than `exp(Lamb(rho_s) - Z + (gamma - q_i)x)` is
`1 + O(sqrt(x/S) + 1/Z)`, which is bounded for `delta` small. The logarithm of the remaining factor
is `O(z_* + x^{3/2} S^{-1/2} + x/S)`, uniformly up to `delta T`. Consistent with the data:
`log 48268 = 10.8 <= 36`. The reversible half of 2(b) is not affected, because there `J` is exactly
linear and `E(z) = C(beta, z)/C(beta, 0)` carries no power of `S`.

The same correction applies to the error term of 2(c), which repeats `sqrt(x/T)(1 + x)` on the
range `1 <= n_i <= delta N`.

### 4.2 The deduction of 2(a) from Lemma L (Section 6.2): complete

I checked every inequality.

- The splitting `e^{q_i x} f_F = Acal + Ecal` with `|Ecal| <= (C/S) Aabs` is immediate from
  Lemma L applied pointwise on the circle. `K_beta = e^{-q_i x} Acal/Lam(0)` holds because the
  integrand is holomorphic on `0 < |z| < 2 z_0`.
- Regime (i), `Z <= Z_0`, with `rho = max(z_*, 1/S)`. On the circle `|x/z| <= Z/2`,
  `|S ab z| <= max(Z/2, ab)` and `|E - 1| = O(1/S)`, because `|c_1 z| + S|z|^2 = O(1/S)`.
  `Acal_0 = Lam(0) z_*^{-1} I_1(Z) >= Lam(0) ab S` (series of `I_1`). `|Acal - Acal_0| <= C Lam(0)`
  and `Aabs <= C Lam(0) S`. Correct. (The bound `|x/z| <= Z_0^2` in the note is loose but harmless.)
- Regime (ii). The real critical point `rho_s` exists by the implicit function theorem in the scaled
  variable `t = z/z_*`, because `R'(z) z_*^2/x = O(1/(ab S) + sqrt(x/S))`. The circle estimate uses
  `R` real on the real axis, `|R''| <= C(1 + S)` on the disc (Cauchy, and `log C` is defined
  because `C(beta, z) != 0` for small `z_0`), and `x/Z <= C sqrt(delta)`. That gives
  `Re Lamb - Lamb(rho) <= -(Z/2)(1 - cos phi)`. The upper bound for `Aabs` follows. For the lower
  bound, `lam(phi) = Lamb(rho e^{i phi})/Z` has `lam(0)` real, `lam'(0) = i rho Lamb'(rho)/Z = 0`,
  `-lam''(0)` in `[1/2, 2]`, and derivatives up to order 4 bounded uniformly. The bound
  `rho^j |R^{(j)}(rho)|/Z = O((1 + x)/Z)` holds by Cauchy estimates on the disc of radius `z_0`.

One formal point (severity 4). Lemma `lem:laplace` of the draft is stated for a compact parameter
space with joint continuity. Here the parameters `(beta, x, S)` with `Z -> infinity` are not
compact. The proof of that lemma uses only the uniform bounds `B_Psi`, `B_a`, `sigma_min`, the gap
`eta` and `epsilon`, and the note supplies all of them explicitly (the gap is the global
`-(1/2)(1 - cos phi)`). So the deduction is sound, but the paper should state a "uniform bounds"
form of the lemma (one sentence) rather than say "the proof uses nothing else".

**Verdict on 6.2.** Complete, given Lemma L.

### 4.3 Section 6.3 (reversible half) and Section 6.4

The reversible computation is correct. `J` linear on the disc by the identity theorem,
`|c_n| <= C z_0^{-n}`, `I_{n-1} <= I_1` for `n >= 2`, and `z_* <= z_0/2` give
`K_beta = B_beta(1 + c_1 z_* I_0/I_1 + O(z_*^2))`. Since `z_* (2/Z) = 1/(ab S)`, both reversible
error claims follow for all `0 < x <= delta T`. The general case `x <= 1` is also fine: the bound
`|I_1 - I_n| <= ((n^2 - 1)/(2 pi)) int e^{Z cos t} t^2 dt` follows from
`cos t - cos nt = 2 sin((n+1)t/2) sin((n-1)t/2)`. For `Z <= Z_0` one has `x = O(1/S)`, so
everything is `O(1/S)`, which is what "regime (i) covers" should say explicitly.

**2(c) needs two inputs, not one (severity 3).** Section 6.4 names the discrete Lemma L (Lemma
`lem:discrete` with complex weights, uniform for `|z| <= z_0`). A second step is also missing: the
discrete analog of Sections 6.2 and 6.3. That is the contour formula of Section 1 above, with kernel
`h w^{-2}(1 - h q_i + h/w)^{n_i - 1}` in place of `e^{x/w} w^{-2}`, and the saddle bounds for it.
The phrase "these produce exactly the Laguerre polynomial `B_{n_i}`" is exact only when
`[z^K] Phi` is replaced by its leading form `f_G (ab S)^K/K!`, that is, in the reversible one-term
approximation. The `e^{-(gamma - q_i)x}` factor of 2(c) needs the discrete saddle argument. That
argument looks routine, because `|1 - h q_i + h e^{-i phi}/rho|` is maximal at `phi = 0` with the
same quadratic decay, but it is not written.

Two smaller slips in 2(c). (1) "up to a factor `1 + O(h)`, uniformly in `n_i`": the Bessel
argument shifts by `(1 - h q_i)^{-1/2}`, which changes `I_1(Z)` by `e^{O(hZ)}`, and `hZ` can be as
large as `C T^2/N`. Also `(1 - h q_i)^{n_i} = e^{-q_i x}(1 + O(hx))`. So the factor is
`1 + O(T^2/N)`, not `1 + O(h)`. That does not change the conclusion, since the replacement is
anyway made at cost `O(T^2/N)`. (2) "For `g = 1` it is exact, see Section 8". The representation
is exact for `g = 1`, but the asymptotic statement 2(c) for `g = 1` (the comparison of
`binom(N' - 1, K)` with `N'^K/K!` and of the start and end terms, uniformly in `n_i`) is not written
in Section 8. Section 8 only identifies the main part. It is easy, because `K <= C T` under the
weights and `K^2/N' = O(T^2/N)`, but it is not done.

## 5. Lemma L

### 5.1 The statement

    Phi(z)(S beta) = S^{-(g-1)/2} C(beta, z) e^{-S J(beta, z)} (1 + eps),  |eps| <= C/S,

uniformly for `beta` in `Kc`, `S >= 1`, complex `|z| <= z_0`, with `J` and `C` holomorphic on
`|z| < 2 z_0`, equal to the rate and constant of `(M(z), pi(z), e(z))` on real `z`, and
`C(beta, 0) = C_G(beta) > 0`. The normalization is right: in occupation coordinates on `G` the
draft's local law reads `S^{-(g-1)} f_S(beta) = S^{-(g-1)/2} C_G e^{-S I_G}`. The hypothesis needs
(H) for `G` (irreducible, `mu(G) > 0`). Without `mu(G) > 0`, `C(beta, 0) = 0` and the relative
statement is false. The deduction uses only (a) holomorphy and non-vanishing of `C` on the disc,
(b) the derivatives of `J` at `0`, which Proposition 3 supplies from the real-`z` identification,
and (c) the pointwise error on circles `|z| <= z_0`. So the statement is exactly what 6.2 needs,
and no more.

### 5.2 Is the route sound? No obstruction found

I checked the four steps of the outline against the proof of Theorem `thm:local` in
`app_torus.tex`.

- **Step 1.** Lemma `lem:torus` uses nonnegativity only to get absolute convergence and the bounds
  `|g| <= g(s')`, `|b| <= b(s')`. With complex weights dominated entrywise by
  `A_G + |z| offdiag(c^- c^+T)`, both survive with the dominating system. The residue at
  `z_1 = g_z(z')` still lies inside `|z_1| = s_1` once `s_1` exceeds the dominating `g`. The new
  end vector changes `b` to `(pi_1 + pi'^T X b_1)(e_1 + a_1^T X e')` by block inversion of
  `pi^T (Z - A)^{-1} e`. Correct.
- **Step 2, the worry that the critical point leaves the real torus.** It does leave the real
  torus, and that is harmless. The integrand is holomorphic in `z'` on a product of annuli
  `|z_j| > theta_j(beta, 0) - delta`, by domination and the regularity paragraph of the draft. So
  the radii may be moved to `rho = |z'_c|` by Cauchy's theorem, and the phase `phi_c` is a
  translation of the torus, which leaves the integral unchanged. For `|z| <= z_0` small, `rho` stays
  in the convergence region because the inequality `varrho(A' - diag theta') < 0` is strict at
  `z = 0`. The phase shift `phi_c` is `O(|z|)`.
- **Step 3, the worry that the real part of the Hessian is not positive.** At the critical point
  the `phi`-Hessian is `-Z_c H(z) Z_c` with `Z_c = diag(z'_c)`. The first-order term
  `z_j d/dz_j` vanishes at a critical point. At `z = 0` it is `Theta' B^T Sigma_beta B Theta'`, real
  and positive definite with least eigenvalue at least `sigma_min > 0` uniformly on `Kc`. It is
  continuous in `(beta, z)` on the compact set `Kc x {|z| <= z_0}`, so `Re Jc >= sigma_min/2` for
  `z_0` small. Positivity fails only for `|z|` of order one, which the deduction never uses (it
  needs `z_* <= z_0/2`, and gets it by taking `delta` small). The gap away from `phi_c` follows from
  the gap at `z = 0` by uniform continuity, provided `|phi_c| < epsilon/2`, which again only needs
  `z_0` small. Near `phi_c`, the bound
  `Re Psi(phi) - Re Psi(phi_c) <= -(sigma_min/8)|phi - phi_c|^2` holds for
  `|phi - phi_c| <= epsilon`, using Taylor with uniform third derivatives.
- **Lemma D.1 with a complex phase.** The proof of `lem:laplace` goes through with
  (i) "`Psi(0)` real" replaced by factoring out `e^{T Psi(0)}`, (ii) the bound
  `|e^{-x^T J x/2}| = e^{-x^T (Re J) x/2}` and `epsilon` chosen against `sigma_min/2`, and
  (iii) `int e^{-x^T J x/2} dx = (2 pi)^{m/2} det(J)^{-1/2}` for complex symmetric `J` with
  `Re J > 0`, with the branch continued from real `J`, a standard identity. The relative error
  needs `|a_0| = |C(beta, z)| * (positive factors)` bounded below, which holds by continuity.
- **Step 4.** Holomorphy of the critical value and amplitude in `z` follows from the holomorphic
  implicit function theorem. Agreement with the real-`z` rate and constant follows from the draft's
  computation for real `0 <= z`, where all weights are nonnegative and the draft's proof applies
  verbatim. Identification on the disc then follows from the identity theorem.

So the outline is correct and I see no missing idea. What is missing is the written proof: a
complex-phase version of Lemma D.1 (about ten lines) and Steps 2 and 3 with explicit constants.
This is severity 2: a named, unproved input whose proof is routine.

### 5.3 A complete short proof for `|G| = 2` (three-state faces)

For `G = {1, 2}` every word alternates, and the word sum is a closed Bessel expression. With
`a_12(z) = q_12 + z c^-_1 c^+_2`, `a_21(z) = q_21 + z c^-_2 c^+_1`, `m = a_12 a_21`,
`zeta = 2 sqrt(m s_1 s_2)`,

    Phi(z)(s) = e^{-<d(z), s>} [ (p_1 e_1 sqrt(m s_1/s_2) + p_2 e_2 sqrt(m s_2/s_1)) I_1(zeta)
                                 + (p_1 a_12 e_2 + p_2 a_21 e_1) I_0(zeta) ],

with `p = pi(z)` and `e = e(z)`. This is the formula behind `two_state_density` in
`08_layer_core.py`. I checked it against the word series at three complex points
(`z = 0.05 + 0.08i`, `-0.07 + 0.02i`, `-0.1i`, at `s = (3, 2)`). The relative difference is
`< 1e-30` (`a3_layer.py`). Now `q_12 q_21 > 0` because `G` is irreducible, so for `|z| <= z_0`
small, `zeta = 2 S sqrt(beta_1 beta_2 m(z))` satisfies `|zeta| >= cS` and `|arg zeta| <= pi/4`.
The uniform large-argument expansion `I_nu(zeta) = e^zeta (2 pi zeta)^{-1/2}(1 + O(1/|zeta|))` for
`|arg zeta| <= pi/2 - epsilon` and `nu = 0, 1` (DLMF 10.40.1 with its error bound) gives Lemma L
with

    J(beta, z) = <d(z), beta> - 2 sqrt(beta_1 beta_2 m(z)),
    C(beta, z) = (4 pi)^{-1/2} (m beta_1 beta_2)^{-1/4} [p_1 e_1 sqrt(m beta_1/beta_2)
                 + p_2 e_2 sqrt(m beta_2/beta_1) + p_1 a_12 e_2 + p_2 a_21 e_1],

and `C(beta, 0) > 0` because `mu(G) > 0`. For real `z >= 0`, `J` is the two-state rate
`I_{M(z)}(beta)`, so Proposition 3 applies. **Consequence: Theorem 2(a), the reversible 2(b), and
the corrected general 2(b) of Section 4.1 hold unconditionally for every face with `|F| = 3` and
`|G| = 2` satisfying (H).** This covers all three chains of the note's numerics, and it is what
Part G (Section 7.3) actually tests. Part G is therefore evidence for the deduction in 6.2, not for
Lemma L when `g >= 3`.

### 5.4 Reversible `Q`, general `g`: a simplification, not a short proof

For reversible `Q`, `M(z)` stays reversible for `nu_G` at complex `z`. The left and right null
vectors `l = sqrt(beta nu)`, `r = sqrt(beta/nu)` of `A(z) - diag theta(z)` with
`theta(z) = A(z) r/r` are then algebraic in `z`. So the critical point is explicit,

    z'_c(beta, z) = theta'(beta, 0) + z b (c^-/r)',

affine in `z`, and Step 2 needs no implicit function theorem. The identity `g_j = -beta_j/beta_1`
continues holomorphically. Step 3 (complex Laplace) is still needed, so this shortens the proof but
does not remove the input. I do not see a proof for general `g` that avoids complex `z`. Real-`z`
asymptotics on `[0, z_0]` plus the domination `|Phi(z)(s)| <= Phi(|z|)(s)` lose a factor
`e^{ab S(|z| - Re z)}` off the positive axis. That is not good enough on the arc
`|arg z| ~ Z^{-1/2}` where the contour integral lives.

## 6. The two corrections to the heuristic

(6a) "Pure Bessel only for `x << T^{1/3}` when non-reversible." Correct, and the reason is right:
the cubic term `S j_3 z_*^3 ~ x^{3/2} T^{-1/2}`. As Section 4.1 shows, the note's own Theorem 2(b)
statement does not respect this correction. The generalized kernel of 2(a) has no such
restriction, and its saddle value is `-(I_F - q_i x)` by the Legendre identity, because the
real-axis saddle of `x/z - S J` is a minimum along the axis. That claim is correct, provided the
saddle lies in `|z| <= z_0`, which holds for `alpha_i <= delta`.

(6b) "No separate lattice sublayer when `T^2/N -> 0`." Correct at the level of the kernel. Lemma
`lem:uniform-laguerre-bessel` gives `0 <= 1 - B_a(w)/(w calI(a w)) <= w/2` for every integer
`a >= 1`, and `w calI(a w) = h sqrt(abS/x) I_1(2 sqrt(abSx))` up to the `1 + O(T^2/N)` factor of
Section 4.3. So the lattice correction is `O(ab T^2/N)` uniformly in `n_i >= 1`. As a statement
about `P_N(n)` for `g >= 2` it inherits the status of 2(c). The sentence "the lattice is felt only
when `n_i <~ ab T^2/N`" is heuristic. Lemma 6.1 shows a uniform deficit of size `w/2`, not one
concentrated at small `n_i`.

## 7. The near-vertex comparison (Section 8)

For `Q = J - dI`, `l = 1`, Lemma 1' with `g = 1` gives
`P_N(b, a) = (1/d) p^{N-1} sum_K binom(a-1, K-1) sum_{r=0}^{2} binom(2, r) binom(b-1, K-r) u^{2K-r}`
with `u = h/p`, under the uniform start. I checked symbolically (`a5_vertex.py`) that this
polynomial equals the draft's `(1 - u)^a E[B_a(v X)]` exactly for `(b, a) = (3,1), (4,2), (5,3),
(6,2)`. For example, both equal `4u^6 + 12u^5 + 16u^4 + 16u^3 + 6u^2 + 2u` at `(5, 3)`. So the
identification "the draft's compound-binomial formula is the probabilistic form of the same sum" is
exact, with the shape-2 gamma variable carrying the start and end terms. The kernel
identification `w calI(a w) = h sqrt(S/x) I_1(2 sqrt(Sx))` with `ab = 1` is correct. The regimes
are correctly separated: the vertex theorem is at `T ~ sqrt N`, where `w` is of order one and the
continuum layer does not apply. The match of error terms (`epsilon = sqrt((|a| + 1)/b)` against
`1/S + sqrt(x/S)`) is a heuristic correspondence, not a theorem, and the `l >= 2` corner paragraph
is a heuristic as well. Both are fine as remarks, labelled as such.

## 8. Other points

- Scope (severity 4). Theorem 2 needs `G = F \ {i}` irreducible with `mu(G) > 0`. Faces where
  removing `i` disconnects `F` (the path `1-2-3` with `i = 2`), or where `mu_G = 0 < mu_i`, are not
  covered. The statement says so through (H), but the summary's "every irreducible `Q`" in
  Proposition 3 should read "every `F` and `i` with `F` and `F \ {i}` irreducible".
- Section 7.1 reading is accurate (two-term lattice ratio within 0.3 to 3.8 percent at `n_3 = 2`).
  Section 7.2 data for the non-reversible chain at `x = T/10, T/4` is the Section 4.1
  counterexample, and should be presented as such rather than as "outside the layer".

## 9. Gaps ranked by severity

1. **Theorem 2(b), general case, and 2(c): false error bound for `x >> T^{1/3}`** (Section 4.1).
   The proof linearizes `exp(O(x^{3/2} T^{-1/2}))`, and numerics give `|E|/bound = 1340` at
   `delta = 0.05`, `T = 3200`. Fix: restrict to `x <= C T^{1/3}`, or use the logarithmic form
   `f_F = f_G B e^{E'}`, `|E'| <= C(1/T + sqrt(x/T)(1 + x))`, up to `delta T`. Also fix the
   summary in Section 0 and Section 9.
2. **Lemma L for `|G| >= 3` is unproved** (Section 5.2). The route is sound and has no
   obstruction for small `z_0`. It needs a written complex-phase Lemma D.1 and Steps 2 and 3 with
   constants. For `|G| = 2` it is proved by the closed Bessel form (Section 5.3), which the note
   should add.
3. **2(c) has a second missing input**: the discrete contour deduction with kernel
   `(1 - h q_i + h/w)^{n_i - 1}` (Section 4.3). There are also two slips: `1 + O(h)` should be
   `1 + O(T^2/N)`, and "exact for `g = 1`" covers the representation, not the asymptotic.
4. Lemma `lem:laplace` is used for a non-compact parameter family in 6.2 regime (ii). The
   uniform-bounds form should be stated. The scope wording in Proposition 3 and in the summary
   should be tightened, and "regime (i) covers" in 6.3 should be made explicit.
5. Wording: in Proposition 2, "no restriction on `x`" holds for the explicit bound, not for the
   `O`-form. The cross-reference in Proposition 3(iii) should be replaced by the coercivity
   argument.

## 10. Verdict per statement

| Statement | Verdict |
|---|---|
| Lemma 1 (continuum representation, (2.1), (2.2)) | Proved as written. Recomputed symbolically. |
| Lemma 1' (discrete representation) | Proved as written. Recomputed in exact rationals. |
| Proposition 2 (pair faces, all `x, s > 0`, two-sided bound) | Proved as written. The `O`-form needs `x <= cT`, which the note says. |
| Proposition 3 (i) Legendre identity | Proved as written. |
| Proposition 3 (ii) `ab`, `j_2`, `gamma - q_i = (ab/2)` times the resistance | Proved as written. |
| Proposition 3 (iii) facet expansion | Proved as written. The one cross-reference should be made self-contained. |
| Proposition 3 (iv) reversible simplifications | Proved as written. |
| Proposition 4 (reversible prefactor matching) | Proved as written. |
| `c_1` formula (reversible) | Proved as written. |
| Lemma L, `|G| = 2` | Proved by the closed Bessel form (Section 5.3 of this audit; not in the note). |
| Lemma L, `|G| >= 3` | Unproved input. The outlined route is sound. Smallest missing piece: a complex-phase Lemma D.1 with `Re J >= sigma_min/2`, and Steps 2 and 3 written for `|z| <= z_0`. |
| Theorem 2(a), `|F| >= 4` | Conditional on Lemma L. The deduction in 6.2 is complete. |
| Theorem 2(a), `|F| = 3` | Proved, using Section 5.3. `|F| = 2`: proved (Proposition 2). |
| Theorem 2(b), reversible, both error claims | Conditional on Lemma L for `|F| >= 4`. Proved for `|F| <= 3`. |
| Theorem 2(b), general | Correct only after a stated restriction: `x <= C T^{1/3}` in the stated relative form, or the logarithmic form up to `delta T`. As written it is false (Section 4.1). Under that restriction it has the same status as 2(a). |
| Theorem 2(c) | Incomplete. Missing: (1) the discrete Lemma L (complex weights, error `O(1/T + T^2/N)`), and (2) the discrete contour deduction with kernel `(1 - h q_i + h/w)^{n_i - 1}`. Its error term needs the same restriction as 2(b). |
| Correction (6a) | Correct. The theorem statement must be made consistent with it. |
| Correction (6b) | Correct at the level of the kernel (Lemma 6.1). For `P_N(n)` with `g >= 2` it has the status of 2(c). |
| Near-vertex comparison (Section 8) | The `l = 1` identification is exact (checked symbolically). The error correspondence and the `l >= 2` corner remark are heuristic and should be labelled so. |

Status: the note's "proved under a stated hypothesis" is accurate for 2(a) and the reversible 2(b),
and is an understatement for `|F| = 3`. For the general 2(b) and for 2(c) it is an overstatement
until the restriction of Section 4.1 is made.
