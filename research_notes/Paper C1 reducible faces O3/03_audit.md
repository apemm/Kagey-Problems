# Paper C1, item O3: audit of Theorem R, Lemmas A to D and Corollary E

Date: 2026-10-25. Read: `01_report.md`, `02_report.md`, and in `paperC` the open question in
`sec_verify.tex`, `def:faces`, `lem:admissible`, `lem:runs`, `lem:continuum`, `lem:upper`,
`thm:first` with `app:first` (Claims A and B), `def:tilt`, `prop:constant`, `thm:local`,
`lem:discrete` (appendix proof), `lem:local-general`, `lem:torus-complex`, `eq:A-sigma`,
`eq:A-Hsigma`, `thm:stratified`, `thm:facemax`, `thm:crossing`, `ex:threecycle`. Nothing in
`paperC` was edited. The scripts of 01 were not rerun; the spot check in Section 5 is a new,
separate computation.

## 1. Claim cards

Notation. `F` admissible, components `C_1, ..., C_r` in path order, `k_j = |C_j|`,
`lambda_j = lambda_{C_j}`, `lambda_F = min lambda_j`, `k*` the least `k_j` with
`lambda_j = lambda_F`, `S* = {j : lambda_j = lambda_F, k_j = k*}`, `a = (k*-1)/2`,
`p_F = a + k_F - k*`, `h = T/N`, `X = N^{-(k_F-1)} T^{p_F} e^{-lambda_F T}
= h^{k_F-1} T^{-a} e^{-lambda_F T}`.

Constant. For `j in S*`, with `r = r_{C_j}`, `l = l_{C_j}`, `l.r = 1`,
`Phi_i(t)_{yx} = e^{-<q,t>} H_{A_{C_i}, e_y, e_x}(t)` (singleton: `e^{-q_i t}`),
`R_i = (q_{xy})_{x in C_i, y in C_{i+1}}`:

    A_j = sup e^{lambda_F |t^<|} mu_{C_1}^T Phi_1 R_1 ... Phi_{j-1} R_{j-1} r      (A_1 = mu_{C_1}.r)
    B_j = sup e^{lambda_F |t^>|} l^T R_j Phi_{j+1} ... R_{r-1} Phi_r 1              (B_r = l.1)
    K = K^red_F = max_{j in S*} A_j B_j / ((2 pi)^a sqrt(det Sigma_{C_j})),

sups over the open orthants of the times of the blocks before (after) `j`. For `k* = 1`
the denominator is 1 and `r = l = 1`. For `r = 1`, `K = K_F`.

- **R(a)** (01). There are `c, C, T_0, N_0` with `c X <= M_F <= C X` for `N >= N_0`,
  `T_0 <= T <= N^{1/3}`.
- **R(b)** (01). `M_F/X -> K` uniformly on `T_eps <= T <= N^{1/3}` (error o(1)).
- **R'** (02, R(b) with a rate). `|M_F/X - K| <= C(1/T + T^2/N)` for `N >= N_1`,
  `T_1 <= T <= N^{1/3}`.
- **Lemma A.** Bridge run expansion of `G(m)_{yx}` and the bounds (2.1) on `kappa_{m'}`.
- **Lemma B / B'.** For `|t| <= R`, `t = hm`: `|G(m)_{yx}/h^{k-1} - phi_{yx}(t)| <= C_R h`;
  the same for finite products (telescoping).
- **Lemma C.** For `m/l` in a compact of `Delta_C^o` and `1 <= s = hl <= l^{1/2}`:
  `G(m)_{yx} = h^{k-1} phi_{yx}(hm)(1 + O(s^2/l))`.
- **Lemma D.** For `l >= l_2`, `s in [s_2, l^{1/3}]`: (i) `max_{|m|=l} G(m)_{yx} <= Y_{yx}(1 +
  C(1/s + s^2/l))`, (ii) `G(m^0)_{yx} >= Y_{yx}(1 - C(1/s + s^2/l))` at a nearest lattice
  point `m^0` to `l alpha*`, with `Y_{yx} = h^{k-1} s^{-a} r_y l_x e^{-lambda s} /
  ((2pi)^a sqrt(det Sigma_C))`.
- **Corollary E.** For admissible `F, G`, `Delta = k_F - k_G >= 1`,
  `delta = lambda_G - lambda_F > 0`, `pi = p_F - p_G`, `kappa = log(K^red_F/K^red_G)`: a zero
  exists in `[(Delta/2delta)L, (2Delta/delta)L]`; every zero in `[T_1, N^{1/3}]` satisfies
  `delta T + pi log T = Delta L - kappa + O(1/L)`; and
  `T_N = (Delta/delta)[L - (pi/Delta) log L + b] + O(log L/L)` with
  `b = -(pi/Delta) log(Delta/delta) - kappa/Delta`.

## 2. The critical step, derived independently

A positive-probability path with support `F` never re-enters a component it has left, so it
visits `C_1, ..., C_r` in blocks of consecutive times; the order is the unique Hamiltonian
path of the condensation DAG, and the block lengths `N_j` are fixed by the composition. The
Markov property at the `r-1` switches gives the exact factorization
`P_N(n) = mu^T G_1 (hR_1) G_2 ... (hR_{r-1}) G_r 1`. Each switch costs `h`; a block of `k_j`
states with time `s_j = hN_j` costs `h^{k_j-1}` times its continuum density, so the powers of
`h` total `sum (k_j - 1) + (r - 1) = k_F - 1`. A block of time `s` in a component with
`lambda_j = lambda_F` and `k_j >= 2` has peak density `s^{-(k_j-1)/2} e^{-lambda_F s}` (the
Gaussian normalization of the local law); a block with `lambda_j > lambda_F` pays
`e^{-(lambda_j - lambda_F)s}`. Splitting the time between two long blocks of rate `lambda_F`
multiplies two such polynomial penalties, which is worse than giving all of it to one block
of least size `k*`; the remaining blocks take time `O(1)` and cost only constants. Hence
`M_F ~ h^{k_F-1} T^{-(k*-1)/2} e^{-lambda_F T}`, and
`k_F - 1 - (k*-1)/2 = (k*-1)/2 + k_F - k* = p_F`. This matches the reports' mechanism.

## 3. Line-by-line check

**Factorization (01 4.1).** Correct. Only starts in `C_1` contribute (no edge back into
`C_1`), so `mu_{C_1}` is right.

**Lemma 2 (01 4.2).** Correct. `theta = q - lambda_j 1 in V_{C_j}`; `hs <= T^2/N <= 1`. The
use of `thm:facemax` with start `e_y`, `l` steps and time `s` is legitimate: `C_j` satisfies
(H) for `mu = e_y`, `h` is the same, `l >= N^{2/3}`, and `s^3 <= l` iff `s^2 T <= N`. Finitely
many starts, so the constants are uniform. For `s < 1`, `lem:upper` alone gives the bound.

**R(a) upper (01 4.3).** Correct. All three cases for `j0` with `s_{j0} >= T/r` give
`w~_{j0} <= C T^{-a}`, using `k_{j0} >= k*` and `T >= 1`.

**Lemma 3 (01 4.3).** Correct. In `W'` the coordinate 1 deviation is at most
`(k*-1)/k* * s'^{-1/2}`, so `n'/l'` stays in a compact; `s'(J_C - lambda_F) <= C_U k*`.
The extension by `m' = ceil(1/h)` visits uses Claim A with `h(m'+1) in [1, 1+2h]`; distinct
`n'` give disjoint events; each interval of length `2a >= 2` holds at least `a` integers, so
`#W' >= a^{k*-1}`, and `#W/#W' <= ((2a + m' + 1)/a)^{k*-1}` is bounded because
`a = s'^{1/2}/(h k*) >= 1/(h k*)`.

**R(a) lower (01 4.3).** Correct. Short blocks: Claim A total `>= c_A` over at most
`(3/h)^{k_j-1}` compositions. Long block: Lemma 3 with `s in [T - 2(r-1), T]`,
`s^{-a} >= T^{-a}`, `e^{-lambda_F s} >= e^{-lambda_F T}`.

**Lemma A.** Correct. The lower bound in (2.1): `prod(1 - j/m_i) >= 1 - sum m'_i(m'_i-1)/(2m_i)`,
`(1-hq_i)^{m_i} e^{hq_i m_i} >= e^{-hq_i^2 t_i}`, and `AB >= 1 - u - w` holds for
`A >= max(0, 1-u)`, `B >= 1 - w >= 0` in both signs of `1 - u`. The case `m'_i > m_i` is
handled since then the right side `>= 1`.

**Lemma B.** Correct. The rewriting `m'(m'-1)/(2m_i) * t^{m'-1}/(m'-1)! = h (m'/2)
t^{m'-2}/(m'-2)!` removes the apparent `1/t_i` singularity, so `C_R` is uniform down to
`t_i = h`. The series with extra factors `M'`, `e^{M'/2}` are entire. B' is a telescoping of
finitely many bounded factors.

**Lemma C.** Correct. The scaling `X_s(s z') = X(z')/s`, `g_s(s z') = s g(z')`,
`b_s(s z') = b(z')` holds for the bridge `b_{yx}` as well (the two factors are each scale
invariant), and `lem:torus-complex` with `(bar A, bar nu, bar e) = (sigma A_C, e_y, e_x)`
gives (4.1). The lower bound for `H_{yx}` comes from `lem:local-general`, which allows
nonnegative nonzero `nu, e`, plus positivity on `[1, s_1] x K`. Steps 2 and 3 repeat the
appendix proof of `lem:discrete`; `h <= hs = s^2/l` for `s >= 1`.

**Lemma D.** Correct after one restriction. As written, (i) maximizes over all `|m| = l`. That
is false: for `m = l e_y` and `x = y`, `G(m)_{yy} = (1-hq_y)^{l-1}`, which is of order 1, not
`h^{k-1}`. The maximum must be over `supp m = C`; `lem:upper` (used outside the ball) requires
full support anyway, and 01 Lemma 3 already states it. The only application (R' case B2)
uses `n^(j)`, which has full support. With that restriction the proof is the proof of
`thm:facemax` with `v = 0`: ball constants from `prop:constant`(a), finitely many
`theta_j in V_C` outside the ball via `J_C = sup_{V_C} <q - theta, .>`, (4.2) from Lemma C and
`lem:local-general`, the concave-quadratic bound `|g|^2/(2 c_U s)`, and (ii) at `|x| <= k/l`.
The same restriction applies to 01 Lemma 4(i).

**(F1), (F2), attainment (02 5.1).** Correct. (F2) passes to the limit in Lemma 2 with
`T = max(|t|, 1)`, `N = T/h -> oo`, which is inside its range. For `k* >= 2` there are no
flat blocks, every factor tends to 0 as its time grows, so `F^<_j`, `F^>_j` attain their
sups on the closed orthants (possibly on the boundary, as in E1 and E4).

**R' upper (02 5.2).** Correct. The crude bound for compositions whose short blocks hold
time `rho >= R_0` is valid because the theorem bounds a maximum, not a sum: in cases A and B1
each `P_N(n) <= K X`, which is below `X(K + C(1/T + T^2/N))`, so no rate is needed there and
`R_0` stays fixed. Case A covers `j0` with `lambda_{j0} = lambda_F`, `k_{j0} > k*` through
`(T/r)^{-(k_{j0}-1)/2} <= C T^{-a-1/2}`. In case B2: Lemma D(i) range holds (`N_j >= N/2`,
`s_j^3 <= N_j`); `kappa_< + kappa_> + k* - 1 = k_F - 1` checks
(`kappa_< = sum_{i<j}(k_i-1) + (j-1)`, `kappa_> = sum_{i>j}(k_i-1) + (r-j)`); B' with the
fixed `R_0` gives the additive `O(h)`; `s_j^{-a} <= T^{-a}(1 + C R_0/T)`; and `h <= T^2/N`.
So the errors are `O(1/T + T^2/N + h) = O(1/T + T^2/N)`. Case `k* = 1`: a flat block is a
1 x 1 factor, so the product factorizes at it, and for every flat `j in S*` the sup of the
product with flat factors 1 equals `A_j B_j`; all flat `j` give the same value, which is `K`.

**R' lower (02 5.3).** Correct. `n^(i) = max(1, ceil(t*/h))` is within `h` per coordinate of
the maximizer, Lipschitz continuity (F1) gives `F(hn) >= A_j - Ch`, B' gives the entrywise
lower bound, Lemma D(ii) the long block, `s^{-a} >= T^{-a}`, and the exponentials combine to
`e^{-lambda_F T}`. For `k* = 1` the flat blocks of length 1 and
`(1-h lambda_F)^{l-1} >= e^{-lambda_F s}(1 - C T^2/N)` close it.

**R(b) of 01.** Its proof leaned on Lemma 4 by inspection; 02 supplies that proof (Lemma D)
and a rate, so R(b) is subsumed by R'.

**01 remark "range down to T = 1".** Not proved (stated as a sketch). Not used by R' or E.

## 4. Corollary E

Subtracting R' for `G` from R' for `F` gives
`D_N = -Delta L + delta T + pi log T + kappa + O(1/T + T^2/N)` on `[T_1, N^{1/3}]`, and R(a)
gives the `O(1)` form. Part 1: continuity and the signs at the two ends are right. Part 2:
for `pi >= 0`, `delta T <= Delta L + O(1)`; for `pi < 0`, `log T <= L/3`; in both cases
`T = O(L)`, then `T = (Delta/delta) L + O(log L)`, and the error is `O(1/L)`. Part 3:
`Xi' = delta + pi/T >= delta/2` on `[cL, CL]`; expanding `log T` and dividing by `delta` gives
`T_N = (Delta/delta)[L - (pi/Delta) log L - (pi/Delta) log(Delta/delta) - kappa/Delta]
+ O(log L/L)`, which is the stated `b`. Checks:

- Irreducible `F`, `G` (or singleton `G`): `p = (k-1)/2`, so `pi/Delta = 1/2` and `b` is
  `b_{FG}` of `thm:crossing`.
- `ex:threecycle`: `p_{1} = 0`; `{1,2}` has components `{1}` (`lambda = b`) and `{2}`
  (`lambda = 1`, flat), so `k* = 1`, `p = 1`; `p_{1,2,3} = 1`. `{1,2}` vs `{1}`: `Delta = 1`,
  `delta = b - 1`, `pi = 1`, coefficient 1. `K^red_{1,2} = A_2 B_2` with
  `A_2 = sup_t b e^{(1-b)t} = b` (at `t -> 0`, i.e. `n_1 = 1`) and `B_2 = 1`; with
  `K_{1} = 1`, `b = log(b-1) - log b = log((b-1)/b)`, matching (ii). `{1,2,3}` vs `{1,2}`:
  `Delta = 1`, `delta = 1`, `pi = 0`, coefficient 0, and `T = L + log b - log K_{1,2,3}
  + O(1/L)`, matching (iii).

Scope: E covers zeros in `[T_1, N^{1/3}]`, not `[1, N^{1/3}]` as in `thm:crossing`(ii), and
it makes no uniqueness claim (the analogue of `thm:crossing`(iv) would need a derivative
lemma on reducible faces). Neither is a defect of the stated result.

## 5. Spot check: `{1} -> {2,3}`, `q12 = q23 = q32 = 1`, start 1

Independent script (not the scripts of 01): the run expansion of the two-state block,
`P = (1-h)^{n_1-1} h sum_M h^{M-1}(1-h)^{l-M} C(n_2-1, m_2-1) C(n_3-1, m_3-1)` with
alternating runs from state 2, maximized over all `n_2` and over `n_1 <= 4`. It agrees with a
brute-force recursion over (composition, state) at `N = 10`, `T = 2` to 1e-16. Here
`k_F = 3`, `k* = 2`, `p_F = 1.5`, `lambda_F = 0`, and `K = r_2 q_12 (l.1)/(sqrt(2pi) *
1/2) = sqrt(2/pi) = 0.797885` (`det Sigma = 1/4` from `prop:constant`(b)).

| N | T | local slope | (M_F/X)/K | maximizer `(n_1, n_2, n_3)` |
|---|---|---|---|---|
| 4000 | 5 | 1.5017 | 1.00052 | (1, 2221, 1778) |
| 4000 | 20 | 1.5025 | 1.00269 | (1, 2051, 1948) |
| 40000 | 3 | 1.5086 | 0.99784 | (1, 23954, 16045) |
| 40000 | 8 | 1.5003 | 1.00006 | (1, 21333, 18666) |
| 40000 | 20 | 1.5003 | 1.00027 | (1, 20512, 19487) |

The slope tends to 1.5, not to the bounds 1 or 2 of `thm:first`(ii); the ratio tends to
`sqrt(2/pi)` with the `1/T` approach at small `T` and the `T^2/N` drift at larger `T`
(compare `N = 4000` with `N = 40000` at `T = 20`). The maximizer has `n_1 = 1`, as the
mechanism predicts.

## 6. Verdicts

| result | verdict |
|---|---|
| Theorem R(a) | proved as written |
| Theorem R(b) (01, o(1)) | proved, via 02's Lemma D; subsumed by R' |
| Theorem R' (rate `O(1/T + T^2/N)`) | proved as written, given Lemma D with the restriction below |
| Lemma A, Lemma B, Corollary B', Lemma C | proved as written |
| Lemma D (and 01 Lemma 4) | correct after a stated restriction: in (i) the maximum is over `supp m = C`; as written it is false (`m = l e_y`) |
| Corollary E | proved as written on `[T_1, N^{1/3}]`; recovers `1/2`, and the `1` and `0` (with constants) of `ex:threecycle` |
| 01 remark: R(a) for `1 <= T <= T_0` | incomplete (sketch only); not needed |

For the paper: state Lemma D(i) with `supp m = C`, and state R' and Corollary E from `T_1`
(or prove the bounded-`T` remark).
