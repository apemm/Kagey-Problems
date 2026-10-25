# C1 full switching range (O2): predictions written before any run (25 October 2026)

No script in this folder had been written or run when this file was saved. Each
prediction is checked in `01_report.md`.

Notation as in Paper C1 (`kagey-problems/problem131/paperC`): `h = T/N`,
`p_i = 1 - h q_i`, `A_F`, `V_F`, `g`, `b` as in app_torus. New: the discrete
Donsker-Varadhan rate of `P = I + hQ`,

    I_h(alpha) = sup_{u>0} sum_i alpha_i log( u_i / (P u)_i ),

and `J_h = I_h / h`, so that `N I_h(n/N) = T J_h(n/N)`.

## Derivation done by hand first

1. Discrete torus formula. The Cauchy identity
   `h^(m-1) C(n-1, m-1) p^(n-m) = (1/2 pi i) oint (p + h z)^(n-1) z^(-m) dz`
   is the discrete version of `t^(m-1)/(m-1)! = (1/2 pi i) oint e^(tz) z^(-m) dz`.
   So Lemma `lem:torus` holds for Good's discrete formula (Lemma `lem:runs`) with
   `e^(t_i z_i)` replaced by `(p_i + h z_i)^(n_i - 1)` and an extra `h^(k-1)`:

       P_N(n) = h^(k-1) (2 pi)^-(k-1) int (p_1 + h g(z'))^(n_1-1)
                prod_{i>=2} (p_i + h z_i)^(n_i-1) b(z') prod_{i>=2} z_i dphi.

   No continuum comparison is needed.
2. With `theta = A u / u` (which runs over `V_F`),
   `I_h(alpha) = sup_{theta in V_F} sum_i alpha_i [-log(1 - h(q_i - theta_i))]`,
   and the real saddle of item 1 is the maximizer. `J_h -> J_F` as `h -> 0`, and
   `J_h = J_F + (h/2) sum_i alpha_i (q_i - theta_i(alpha))^2 + O(h^2)`.
3. In the variable `z` every object is real-analytic in `(h, alpha)` on
   `[0, h_*] x Delta_F^o`, including `h = 0`, where it is the continuum object.
   Laplace's lemma with parameter space `[0, h_*] x K` then gives the local law
   with relative error `O(1/T)` uniformly for `1 <= T <= h_* N`, for any fixed
   `h_* < 1/q_max`.
4. The constant is
   `C_F^(h)(alpha) = c_h (mu.r)(l.1) sqrt(det Hess J_h(alpha) / (2 pi)^(k-1))`,
   with `r, l` the Perron vectors of `A_F - diag theta^h(alpha)`, `l.r = 1`, and
   `c_h = sum_i alpha_i / (1 - h(q_i - theta_i))`. At `h = 0`, `c_0 = 1` and this
   is `C_F` of Proposition `prop:constant`(a).
5. The minimum of `I_h` on a face is `-log(1 - h lambda_F)`, attained at the
   same `alpha*_F = l_F o r_F` for every `h`. So
   `M_F = N^-(k-1) T^((k-1)/2) K_F^(h) (1 - h lambda_F)^N (1 + O(1/T))` with
   `K_F^(h) = C_F^(h)(alpha*_F)`, which carries a factor `1/(1 - h lambda_F)`.
   For a vertex this matches `mu_i (1 - h q_i)^(N-1)` exactly.

## Numerical predictions

Two-state chain `q12 = 1`, `q21 = 2`, `N = 4000`, `alpha = n_1/N`.

- **P1 (exactness).** A log-space forward recursion and Good's run sum
  (log-space, `lgamma`) agree to relative `1e-9` for every `n` at `N = 4000`,
  and both agree with brute-force enumeration for `N <= 14` to `1e-12`.
- **P2 (plan's table).** The spread over `alpha in [0.45, 0.85]` of
  `log P_N(n) + exponent` reproduces the plan within `0.01`:
  `T J_V`: 0.336, 0.341, 2.34, 10.1; `N I_h`: 0.340, 0.341, 0.333, 0.315 for
  `T = 16, 63, 200, 400`. The plan does not state the start; I expect the
  uniform start and say so if it fails and the stationary one matches.
- **P3 (the constant).** The two formulas for `C_F^(h)` (item 4, and the torus
  form `b(theta') / ((2 pi)^((k-1)/2) prod(p_i + h theta_i) sqrt(det H_h))`) agree
  to `1e-6`. The ratio `R = P_N(n) / (N^-1 T^(1/2) C^(h) e^(-N I_h))` has
  `T |R - 1| <= 3` on the grid, for `T` from 16 to 1000 (`h` up to 0.25), and
  `T (R - 1)` changes little between `T = 200` and `T = 1000`.
- **P4 (the `T^2/N` term).** `N I_h - T J_V` equals
  `(T^2/(2N)) sum alpha_i (q_i - theta_i)^2` up to relative `O(h)` (below 15% at
  `h = 0.1`).
- **P5 (a proper face).** Three states, face `{1,2}` with exit rates. `M_F`
  divided by the new prediction is `1 + O(1/T)` up to `T = N/10` (within 5% for
  `T >= 40`), while the old prediction with `e^(-T lambda_F)` and `K_F` is off by
  a factor near `exp(-T^2 lambda_F^2 / (2N))` times `1 + O(h)`.
- **P6 (three free coordinates, non-reversible).** For a non-reversible
  three-state chain, full face, `N = 600`, the ratio `R` is within `C/T` of 1 at
  interior points, `T in {20, 40, 60}`.
- **P7 (literature).** None of Miller (1961), Kontoyiannis-Meyn (2003, Thm 6.3),
  Herve-Ledoux (2013) states uniformity as `P -> I`; their constants depend on
  the spectral gap and the non-lattice/aperiodicity margin of a fixed kernel.
