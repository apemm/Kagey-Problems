# Problem 131 Paper D, topic D1 ledger (elephant random walk, center vs endpoint crossing): predictions with kill conditions, written before the computations that test them; outcomes appended verbatim below each.

Conventions for every entry. Elephant walk: X_1 = +1 or -1 with probability 1/2 (symmetric start); step t+1 copies a uniformly chosen earlier step and flips it with probability eps. A_n = number of +1 steps, h = n/2, b_t = number of steps among the first t that differ from X_1. Center C_n(eps) = P(A_n = h) = P(b_n = h). Endpoint E_n(eps) = P(A_n = n) = (1/2)(1-eps)^(n-1). Crossing x_n = n*eps_n with E_n = C_n. pi_t = u_{t+1}(1) = t*prod_{i=1}^{t-1}(h-i) / prod_{i=1}^{t}(n-i) (Polya urn (t,1) hits h). Lambda_n(eps) = eps * sum_t (1-eps)^(t-1) pi_t. c_j(n) = coefficient of eps^j in C_n(eps).

## 2026-09-25, batch 1 (written before any D1 code was run)

**D1-P1 (reproduction).** erw.py, run unchanged, prints x_3200 = 11.547 and heuristic root 11.611 (the values in program.md). An independent DP (fixed start, window b in [max(0,h-n+t), min(t-1,h)], in-place numpy) gives the same x_n as erw.py for every n in {50,100,200,400,800,1600,3200}.
Kill: x_3200 from erw.py does not round to 11.547, or |x_n(mine) - x_n(erw.py)| > 1e-6 at any n.

**D1-P2 (exact identities, proved in D1.md before running).** (a) Duhamel identity C_n = eps * sum_{t=1}^{n-1} E[g_t(b_t)], g_t(b) = 2(t-2b)^2 H'_t(b) / (t(n-t)), H'_t(b) = C(t,b)C(n-t,h-b)/C(n,h), holds to relative error < 1e-9 for n in {10, 40, 200, 1000} and eps in {0.001, 0.05, 0.3}. (b) Lambda_n(eps) <= C_n(eps) in every cell computed in this topic. (c) For n >= 20: n(1+eps)^2 Lambda_n / (4 eps) lies in [1 - 14/n, 1 + 6/n]. (d) float64 DP agrees with an exact rational DP (Fraction, eps = 1/20 and 3/100) at n in {10, 30, 60} to relative 1e-12, and with a 40-digit mpmath DP at n = 400 to relative 1e-10.
Kill: any single violation.

**D1-P3 (first order, proved).** c_1(n) = sum_t pi_t and |n c_1(n)/4 - 1| <= 6/n for n >= 20.
Kill: any violation for n in {20, 50, 100, 400, 1600, 3200}.

**D1-P4 (second order, heuristic from the Gronwall rate 2/t).** K_2(n) := c_2(n)/c_1(n) - 2 log n converges to a finite constant kappa: over n = 100, 200, ..., 3200 the successive differences |K_2(2n) - K_2(n)| decrease, the last one is < 0.05, and |kappa| <= 5. A rough back-of-envelope from the program.md numbers at n = 3200 suggests kappa is near -1.6 (not a kill condition, just recorded).
Kill: successive differences do not decrease, or the last one is >= 0.05, or |K_2(3200)| > 5.

**D1-P5 (exponentiated form, heuristic).** The eps^2 log^2 n term is captured by exponentiating: D_3(n) := c_3/c_1 - (c_2/c_1)^2/2 satisfies |D_3(n)| / (c_2/c_1)^2 < 0.25 at n = 3200 and this ratio decreases in n over 100..3200.
Kill: ratio >= 0.25 at n = 3200, or ratio increasing over the last three doublings.

**D1-P6 (refined crossing, heuristic).** Let xhat_n solve (1/2)(1-x/n)^(n-1) = c_1(n) (x/n) exp((x/n) c_2(n)/c_1(n)). Then |xhat_n - x_n| <= 0.01 for n in {400, 800, 1600, 3200} and <= 0.002 at n = 3200. The leading-order root g_n of x + log x = 2 log n - log 8 overshoots: x_n < g_n for all n >= 100.
Kill: any of these fails.

### Outcomes of batch 1 (2026-09-25; scripts D1_erw.py, D1_batch1.py; raw output D1_out_batch1.txt and D1_out_erw_original.txt in the scratchpad code folder)

erw.py unchanged printed: n=3200 x_n=11.5468, heuristic x=11.6105 (full table in D1_out_erw_original.txt).

```
== P1 reproduction ==
n=   50 x_mine=3.9404868665 x_erw=3.9404868665 diff=0.00e+00 leading g=4.288636
n=  100 x_mine=5.0958966738 x_erw=5.0958966738 diff=7.11e-15 leading g=5.437567
n=  200 x_mine=6.3405901682 x_erw=6.3405901682 diff=5.33e-15 leading g=6.626167
n=  400 x_mine=7.6292168962 x_erw=7.6292168962 diff=1.78e-14 leading g=7.843768
n=  800 x_mine=8.9334617102 x_erw=8.9334617102 diff=-1.24e-14 leading g=9.083340
n= 1600 x_mine=10.2405649147 x_erw=10.2405649147 diff=1.60e-14 leading g=10.340051
n= 3200 x_mine=11.5468344808 x_erw=11.5468344808 diff=4.80e-14 leading g=11.610464
== P2a Duhamel identity ==  (largest relative error over the 12 cells)
n= 1000 eps=0.3: center=1.258718875702526e-02 duhamel=1.258718875701600e-02 rel=7.36e-13
== P2d rational / mpmath checks ==  (largest relative errors)
n=60 eps=3/100: exact=2.30346816094347245e-03 float=2.30346816094347028e-03 rel=9.41e-16
n=400 eps=7.6292/400: mp=0.0002301442712452585376358557 float=2.30144271245258700e-04 rel=7.07e-16
== P2b/P2c/P3 main term ==
n=   20 n c1/4 = 0.9090909091  (n c1/4 - 1)*n = -1.818182
n= 3200 n c1/4 = 0.9993753904  (n c1/4 - 1)*n = -1.998751
C>=Lambda: True in all 18 cells; (Lambda-norm - 1)*n ranged over [-1.9950, +0.0645]
n= 3200 x=16.1418: Lambda-norm=0.99939408 C/Lambda=1.08691672 (C/Lambda)/n^(2eps)=1.001922
== P4/P5 Taylor coefficients ==
n=  100 c2/c1=7.26322055 K2=-1.94711982 D3=-9.737599 D3/(c2/c1)^2=-0.18458
n=  200 c2/c1=8.80919115 K2=-1.78744358 D3=-9.805378 D3/(c2/c1)^2=-0.12635
n=  400 c2/c1=10.29809351 K2=-1.68483559 D3=-9.606712 D3/(c2/c1)^2=-0.09059
n=  800 c2/c1=11.74675491 K2=-1.62246855 D3=-9.355516 D3/(c2/c1)^2=-0.06780
n= 1600 c2/c1=13.16963960 K2=-1.58587822 D3=-9.138494 D3/(c2/c1)^2=-0.05269
n= 3200 c2/c1=14.57689066 K2=-1.56492152 D3=-8.977048 D3/(c2/c1)^2=-0.04225
K2 successive differences: +0.159676, +0.102608, +0.062367, +0.036590, +0.020957
== P6 refined crossing ==
n=  400 x_n=7.629217 xhat=7.626166 diff=-0.003050  x_n-g_n=-0.214551
n=  800 x_n=8.933462 xhat=8.932419 diff=-0.001042  x_n-g_n=-0.149878
n= 1600 x_n=10.240565 xhat=10.240225 diff=-0.000340  x_n-g_n=-0.099487
n= 3200 x_n=11.546834 xhat=11.546727 diff=-0.000107  x_n-g_n=-0.063629
```

Verdicts: D1-P1 survives. D1-P2 (a)-(d) survive. D1-P3 survives; unexpected exact form n c_1(n)/4 = n/(n+2), i.e. c_1(n) = 4/(n+2) at every n tested. D1-P4 survives (differences decrease, last 0.021 < 0.05, K2(3200) = -1.565). D1-P5 survives (ratio -0.042, magnitude decreasing). D1-P6 survives (all diffs <= 0.0031, 0.00011 at n = 3200; x_n < g_n throughout).

## 2026-09-25, batch 2 (written before any batch-2 code was run; proofs referred to are in D1.md)

Extra notation. gamma = eps/(1-2eps), a = 2eps/(1-4eps), c_s = a(s+10). Phi^c_s(b) = C(n-s,h-b) B(h+c,h+c)/B(b+c,s-b+c) (Polya urn with pseudo-count c on each colour hits h). V_s(b) = P(b_n = h | b_s = b) for the eps-chain. D_s(b) = [(1-r)Phi^{c_{s+1}}_{s+1}(b) + r Phi^{c_{s+1}}_{s+1}(b+1)] / Phi^{c_s}_s(b), r = eps + (1-2eps) b/s. Sigma_s = s + 2c_s. Bridge = Polya chain conditioned on b_n = h (up-probability (h-b)/(n-s)). w_t = pi_t/c_1. g(t) = (t+11)(log((t+1)^2/(4t)) + 2/3) - H_t + 2/(3t). U_n(eps) = eps c_1 exp(a H_{n-1}) sum_t w_t (1-eps)^(t-1) exp(a g(t)) (proved upper bound). J_n(eps) = eps sum_{t<=T} (1-eps)^(t-1) pi_t exp(eps A_t - eps^2 B_t) with A_t = sum_u E_bridge theta_u, theta_u(b) = n(u-2b)^2/(2(n-u)b(u-b)), B_t = sum_u E_bridge[(1-2f)^2 (pi/f^2 + (1-pi)/(1-f)^2)] (proved lower bound, T = min(h, 60)). kappa_2(n) = c_2/c_1, K_2(n) = kappa_2(n) - 2 log n.

**D1-P7 (proved identities and bounds; checks for algebra/code errors).**
(a) Closed form: D_s(b) = J * Phi^{c'}_s(b)/Phi^c_s(b) with J = 1 - (rho-1) u (u+v)/(1/4-u^2), d = s/2-b, u = d/(s+2c'), v = d/(n-s), rho = (s+2c')/(s(1+2gamma)); agrees with direct evaluation of D_s(b) to relative 1e-11 at every feasible state, n in {40, 200}, eps in {0.001, 0.05, 0.2}.
(b) Supersolution inequality: max over feasible (s,b) of log D_s(b) - a/Sigma_s - 2a/(3 Sigma_s^2) is <= 1e-12 for n in {40, 200, 1000}, eps in {0.001, 0.01, 0.05, 0.2}.
(c) C_n <= U_n in every cell n in {50,100,...,3200} x {x_n/2, x_n, 2 x_n}/n; at the crossing of n = 3200, U_n/C_n lies in [1.00, 1.25].
(d) Lambda_n <= J_n <= C_n in the same cells; at the crossing of n = 3200, J_n/C_n lies in [0.99, 1.00].
Kill: any violation of (a)-(d).

**D1-P8 (exact second coefficient).** kappa_2(n) = sum_t w_t [A_t - (t-1)] (bridge formula, A_t as in J_n with all t <= h) equals the Taylor-DP value c_2/c_1 to relative 1e-9 at n in {100, 400, 1600}.
Kill: any relative discrepancy > 1e-9.

**D1-P9 (limit constant, heuristic limit interchange).** K_2 := sum_t t 2^(-t-1) [A_t^inf - (t-1)], A_t^inf = lim_U (sum_{u=t+1}^U e_u - 2 log U), e_u = E[(u-2B)^2/(2B(u-B))], B = 1 + Bin(u-t-1, 1/2). Prediction: K_2 lies in [-1.555, -1.525] (extrapolation of batch-1 K_2(n): -1.539).
Kill: K_2 outside [-1.555, -1.525].

**D1-P10 (Taylor DP at new sizes).** K_2(6400) = -1.5531 +- 0.003 and K_2(12800) = -1.5466 +- 0.003 (successive-difference ratios 0.56, 0.555 continued from batch 1).
Kill: either outside its interval.

**D1-P11 (Guerin-Laulin-Raschel-Simon check and mixture).** At the crossing eps_n for n in {50,100,...,3200}: the fixed-start law of b_n is unimodal (GLRS finite-n unimodality with q = 1); the symmetric-start law of A_n is not unimodal; P_sym(A_n = n-1)/P_sym(A_n = n) >= x_n/(2(1-eps_n)) (proved bound).
Kill: fixed-start law not unimodal in some cell, or the bound fails.

**D1-P12 (monotone likelihood ratio, proved).** For n in {10, 50, 400}, C_n(eps)/E_n(eps) is strictly increasing on the grid eps = 0.001, 0.002, ..., 0.999, and so is P(b_n = k)/P(b_n = 0) for every k in 1..n-1 (n = 10, 50 only).
Kill: any non-increase beyond relative 1e-12.

### Outcomes of batch 2, part 1 (2026-09-25; scripts D1_lib2.py, D1_batch2.py; raw output D1_out_batch2_P7a_P7b.txt, D1_out_batch2_P7cd_P8.txt, D1_out_batch2_P9_P11_P12.txt)

```
== P7a closed form of D_s(b) ==
n=40 eps=0.001: max |logD_direct - logD_formula| = 2.71e-14
n=40 eps=0.05: max |logD_direct - logD_formula| = 2.89e-14
n=40 eps=0.2: max |logD_direct - logD_formula| = 3.13e-13
n=200 eps=0.001: max |logD_direct - logD_formula| = 2.88e-13
n=200 eps=0.05: max |logD_direct - logD_formula| = 4.25e-13
n=200 eps=0.2: max |logD_direct - logD_formula| = 1.68e-12
bridge second moment closed form: max rel err = 6.20e-16
== P7b supersolution inequality ==
n=40 eps=0.001: max[logD - a/Sig - 2a/(3Sig^2)] = -5.081e-05; max Sig*logD/a = 1.1697 (0.0s)
n=40 eps=0.01: max[logD - a/Sig - 2a/(3Sig^2)] = -5.041e-04; max Sig*logD/a = 1.1137 (0.0s)
n=40 eps=0.05: max[logD - a/Sig - 2a/(3Sig^2)] = -2.436e-03; max Sig*logD/a = 0.9521 (0.0s)
n=40 eps=0.2: max[logD - a/Sig - 2a/(3Sig^2)] = -8.647e-03; max Sig*logD/a = 0.4125 (0.0s)
n=200 eps=0.001: max[logD - a/Sig - 2a/(3Sig^2)] = -1.003e-05; max Sig*logD/a = 1.2112 (0.0s)
n=200 eps=0.01: max[logD - a/Sig - 2a/(3Sig^2)] = -1.002e-04; max Sig*logD/a = 1.1637 (0.0s)
n=200 eps=0.05: max[logD - a/Sig - 2a/(3Sig^2)] = -4.974e-04; max Sig*logD/a = 1.0447 (0.1s)
n=200 eps=0.2: max[logD - a/Sig - 2a/(3Sig^2)] = -1.939e-03; max Sig*logD/a = 0.7709 (0.0s)
n=1000 eps=0.001: max[logD - a/Sig - 2a/(3Sig^2)] = -2.001e-06; max Sig*logD/a = 1.2194 (0.3s)
n=1000 eps=0.01: max[logD - a/Sig - 2a/(3Sig^2)] = -2.001e-05; max Sig*logD/a = 1.1737 (0.3s)
n=1000 eps=0.05: max[logD - a/Sig - 2a/(3Sig^2)] = -9.989e-05; max Sig*logD/a = 1.0644 (0.2s)
n=1000 eps=0.2: max[logD - a/Sig - 2a/(3Sig^2)] = -3.975e-04; max Sig*logD/a = 0.9236 (0.3s)
== P7c/P7d rigorous bounds ==
n=   50 x=  1.9702: Lambda/C=0.757391 J/C=0.978458 U/C=3.792351 order_ok=True
n=   50 x=  3.9405: Lambda/C=0.590618 J/C=0.914915 U/C=69.527830 order_ok=True
n=   50 x=  7.8810: Lambda/C=0.390091 J/C=0.714145 U/C=222392646749194518528.000000 order_ok=True
   (0.0s)
n=  100 x=  2.5479: Lambda/C=0.797575 J/C=0.988081 U/C=2.200142 order_ok=True
n=  100 x=  5.0959: Lambda/C=0.645136 J/C=0.951927 U/C=7.646177 order_ok=True
n=  100 x= 10.1918: Lambda/C=0.440756 J/C=0.822061 U/C=1294131.571544 order_ok=True
   (0.1s)
n=  200 x=  3.1703: Lambda/C=0.845619 J/C=0.994393 U/C=1.581017 order_ok=True
n=  200 x=  6.3406: Lambda/C=0.719082 J/C=0.977232 U/C=2.879222 order_ok=True
n=  200 x= 12.6812: Lambda/C=0.529246 J/C=0.910059 U/C=24.524266 order_ok=True
   (0.3s)
n=  400 x=  3.8146: Lambda/C=0.890450 J/C=0.997650 U/C=1.300559 order_ok=True
n=  400 x=  7.6292: Lambda/C=0.794473 J/C=0.990480 U/C=1.770084 order_ok=True
n=  400 x= 15.2584: Lambda/C=0.636376 J/C=0.961514 U/C=3.973232 order_ok=True
   (0.7s)
n=  800 x=  4.4667: Lambda/C=0.926495 J/C=0.999094 U/C=1.160879 order_ok=True
n=  800 x=  8.9335: Lambda/C=0.858957 J/C=0.996344 U/C=1.367595 order_ok=True
n=  800 x= 17.8669: Lambda/C=0.739791 J/C=0.985192 U/C=2.000061 order_ok=True
   (1.5s)
n= 1600 x=  5.1203: Lambda/C=0.952736 J/C=0.999671 U/C=1.087489 order_ok=True
n= 1600 x= 10.2406: Lambda/C=0.907896 J/C=0.998677 U/C=1.188228 order_ok=True
n= 1600 x= 20.4811: Lambda/C=0.824976 J/C=0.994661 U/C=1.440732 order_ok=True
   (3.9s)
n= 3200 x=  5.7734: Lambda/C=0.970573 J/C=0.999886 U/C=1.047848 order_ok=True
n= 3200 x= 11.5468: Lambda/C=0.942074 J/C=0.999542 U/C=1.099629 order_ok=True
n= 3200 x= 23.0937: Lambda/C=0.887736 J/C=0.998158 U/C=1.216717 order_ok=True
   (9.7s)
== P8 kappa_2 bridge formula vs Taylor DP ==
n=100: kappa2 bridge=7.263220550717 taylorDP=7.263220550717 rel=2.19e-14 K2=-1.94711982 (0.2s)
n=400: kappa2 bridge=10.298093506560 taylorDP=10.298093506560 rel=2.57e-14 K2=-1.68483559 (1.0s)
n=1600: kappa2 bridge=13.169639599683 taylorDP=13.169639599680 rel=2.69e-13 K2=-1.58587822 (5.5s)
== P9 limit constant K_2 ==
U0=1500: K_2 = -1.53873234 (23.0s)
   t=1: A_t^inf=-2.23186348
   t=2: A_t^inf=-2.23186348
   t=3: A_t^inf=-0.73186882
   t=4: A_t^inf=1.43478717
   t=5: A_t^inf=4.01810448
   t=6: A_t^inf=6.90141644
   t=7: A_t^inf=10.01805636
   t=8: A_t^inf=13.32516708
U0=3000: K_2 = -1.53871997 (83.6s)
   t=1: A_t^inf=-2.23186314
   t=2: A_t^inf=-2.23186314
   t=3: A_t^inf=-0.73186448
   t=4: A_t^inf=1.43479952
   t=5: A_t^inf=4.01812885
   t=6: A_t^inf=6.90145685
   t=7: A_t^inf=10.01811684
   t=8: A_t^inf=13.32525168
== P11 GLRS unimodality (fixed start) and symmetric mixture ==
n=   50 x=3.9405: fixed-start unimodal=True (mode b=4); sym sign changes=3 sym max at k=4, Q(h)/Q(n)=1.000000; Q(n-1)/Q(n)=2.2368 >= bound 2.1388: True
n=  100 x=5.0959: fixed-start unimodal=True (mode b=7); sym sign changes=3 sym max at k=7, Q(h)/Q(n)=1.000000; Q(n-1)/Q(n)=2.7595 >= bound 2.6848: True
n=  200 x=6.3406: fixed-start unimodal=True (mode b=10); sym sign changes=3 sym max at k=10, Q(h)/Q(n)=1.000000; Q(n-1)/Q(n)=3.3288 >= bound 3.2741: True
n=  400 x=7.6292: fixed-start unimodal=True (mode b=13); sym sign changes=3 sym max at k=13, Q(h)/Q(n)=1.000000; Q(n-1)/Q(n)=3.9270 >= bound 3.8888: True
n=  800 x=8.9335: fixed-start unimodal=True (mode b=17); sym sign changes=3 sym max at k=17, Q(h)/Q(n)=1.000000; Q(n-1)/Q(n)=4.5428 >= bound 4.5172: True
n= 1600 x=10.2406: fixed-start unimodal=True (mode b=21); sym sign changes=3 sym max at k=21, Q(h)/Q(n)=1.000000; Q(n-1)/Q(n)=5.1699 >= bound 5.1533: True
n= 3200 x=11.5468: fixed-start unimodal=True (mode b=25); sym sign changes=3 sym max at k=25, Q(h)/Q(n)=1.000000; Q(n-1)/Q(n)=5.8048 >= bound 5.7943: True
== P12 monotone likelihood ratio in eps ==
n=10: min increment of log(C/E) over grid = 1.665e-02 (strict: True)
   all k: min increment of log P(b_n=k)/P(b_n=0) = 5.805e-03
n=50: min increment of log(C/E) over grid = 6.739e-02 (strict: True)
   all k: min increment of log P(b_n=k)/P(b_n=0) = 5.978e-03
n=400: min increment of log(C/E) over grid = 4.492e-01 (strict: True)
```

Verdicts: D1-P7 (a)-(d) survive (at the n = 3200 crossing U/C = 1.0996 and J/C = 0.99954; the upper bound is useless at small n and large x, e.g. U/C = 2.2e20 at n = 50, x = 7.9, as expected since it needs a log n small). D1-P8 survives (relative 2e-14 to 3e-13). D1-P9 survives: K_2 = -1.53872 (U0 = 3000; -1.53873 at U0 = 1500). Unexpected: A_1^inf = A_2^inf = -2.2318631 = 2(gamma_E - 1 - log 2) (closed form found after the run, see D1.md). D1-P11 survives in all seven cells; the symmetric law has exactly 3 sign changes of its first difference (W shape). D1-P12 survives.

## 2026-09-25, batch 2 part 2 (written after part 1, before any DP at n = 6400 or 12800)

Predictions come from D1_predict.py (no DP at the new sizes). Calibration on the old sizes: with exact kappa_2 and kappa_3 = c_3/c_1 - kappa_2^2/2, the refined equation log(4x/(n(n+2))) + (x/n) kappa_2 + (x/n)^2 kappa_3 = log(1/2) + (n-1) log(1-x/n) misses x_3200 by -5.3e-7. For the new sizes kappa_2 = 2 log n + K_2 + delta_n with K_2 = -1.53872 and delta_n = -(12.3 log n - 15.8)/n (fit to batch 1), kappa_3 = -8.85 (6400), -8.75 (12800) (extrapolated).

**D1-P13 (crossing at n = 6400 and 12800).**
(a) Leading root g_n of x + log x = 2 log n - log 8: 12.892054 (6400), 14.182921 (12800). Proved: x_n < g_n and g_n - x_n = O((log n)^2/n). Prediction: g_n - x_n in [0.035, 0.045] (6400) and [0.020, 0.028] (12800).
(b) Proved second-order root x_2nd = g_n - (2 g_n log n + g_n^2/2)/(n(1+1/g_n)) (error O(log n / n)): 12.847237 (6400), 14.156003 (12800). Prediction: x_n - x_2nd in [0.003, 0.008] (6400) and [0.0015, 0.0045] (12800).
(c) Refined (heuristic, K_2 and kappa_3): x_6400 = 12.852483 +- 2e-5 and x_12800 = 14.158845 +- 1.5e-5.
(d) The forward window DP and an independent backward DP (value function, folded by the symmetry V_s(b) = V_s(s-b)) agree on C_n at the crossing to relative 1e-11.
(e) Rigorous bounds at the crossing: Lambda_n <= J_n <= C_n <= U_n, with U_n/C_n in [1.00, 1.08] and J_n/C_n in [0.9995, 1.0] at both sizes.
Kill: any of (a)-(e) fails.

### Outcomes of batch 2 part 2 and D1-P10 (2026-09-25; script D1_batch3.py; raw output D1_out_batch3_P13_P10.txt)

```
== P13 crossing at new sizes ==
n=6400: x_n=12.8524830457 (0.5s)  C_fwd=1.295592431434982e-06 C_bwd=1.295592431434981e-06 rel=8.17e-16 E=1.295592431434990e-06
   g_n - x_n = 0.039571 (g_n=12.892054); x_n - x_2nd = 0.005246; x_n - x_ref = +4.566e-08
   Lambda/C=0.964588 J/C=0.9998467 U/C=1.053518 order_ok=True (16.2s)
n=12800: x_n=14.1588452626 (1.8s)  C_fwd=3.523212542627939e-07 C_bwd=3.523212542627994e-07 rel=1.56e-14 E=3.523212542627917e-07
   g_n - x_n = 0.024076 (g_n=14.182921); x_n - x_2nd = 0.002842; x_n - x_ref = +2.626e-07
   Lambda/C=0.978817 J/C=0.9999500 U/C=1.028900 order_ok=True (45.3s)
== P10 Taylor DP K_2(n) ==
n=6400: c1*(n+2)/4=1.000000000000 kappa2=15.9749810864 K2=-1.55312545 kappa3(D3)=-8.866333 (0.5s)
n=12800: c1*(n+2)/4=1.000000000000 kappa2=17.3678284386 K2=-1.54657246 kappa3(D3)=-8.794224 (1.9s)
```

Verdicts: D1-P13 (a)-(e) all survive. x_6400 = 12.8524830457 (refined prediction 12.852483, miss +4.6e-8); x_12800 = 14.1588452626 (prediction 14.158845, miss +2.6e-7). D1-P10 survives: K_2(6400) = -1.553125, K_2(12800) = -1.546572. The exact identity c_1 = 4/(n+2) holds at both new sizes to 12 digits.

## 2026-09-25, batch 3 (written before running D1_batch4.py)

**D1-P14 (fixed eps, superdiffusive side; heuristic).** If log C_n(eps) = log(4 eps/(n+2)) + eps kappa_2(n) + eps^2 kappa_3(n) + ... with kappa_2 = 2 log n + K_2 + o(1) and kappa_3 bounded, then for fixed eps the ratio R_n(eps) := C_n(eps) (n+2) n^(-2 eps) / (4 eps) converges, and the ERW local limit (P(S_n = 0) ~ 2 phi_{L_1}(0) n^(-a), a = 1 - 2 eps) gives phi_{L_1}(0) = (1-a) R_inf(eps). Prediction, using K_2 = -1.53872 and kappa_3 = -8.8: R_12800(0.01) = 0.9839 +- 0.002, R_12800(0.02) = 0.9665 +- 0.003, R_12800(0.05) = 0.906 +- 0.012; and |R_12800 - R_6400| < 0.001 for eps = 0.01 and 0.02.
Kill: any value outside its interval, or the 6400-to-12800 change >= 0.001 at eps = 0.01 or 0.02.

### Outcome of batch 3 (2026-09-25; script D1_batch4.py; raw output D1_out_batch4.txt)

```
eps=0.01: n=800: R=0.982973  n=1600: R=0.983354  n=3200: R=0.983577  n=6400: R=0.983704  n=12800: R=0.983776
eps=0.02: n=800: R=0.964352  n=1600: R=0.965141  n=3200: R=0.965610  n=6400: R=0.965884  n=12800: R=0.966042
eps=0.05: n=800: R=0.899131  n=1600: R=0.901218  n=3200: R=0.902543  n=6400: R=0.903367  n=12800: R=0.903871
```

Verdict: D1-P14 survives (0.983776, 0.966042, 0.903871; changes 6400 -> 12800 are 7.2e-5 and 1.6e-4). R_n increases slowly in n, consistent with K_2(n) increasing to K_2. This is evidence for the heuristic phi_{L_1}(0) = (1-a) exp(K_2 (1-a)/2 + O((1-a)^2)), not a proof.

## 2026-09-25, batch 4: revision after two verification passes (written before any batch-4 code was run, except the formula-only predictor D1_fix_predict.py, whose output D1_fix_out_predict.txt is quoted below)

Erratum to the D1-P13 outcome above (appended, nothing above is changed). The misses "+4.6e-8" (6400) and "+2.6e-7" (12800) were measured against the registered 6-decimal values 12.852483 and 14.158845, so they are dominated by rounding (up to 5e-7). D1_fix_out_predict.txt: against the unrounded formula-only predictions of D1_predict.py (12.8524828387, 14.1588451987) the misses are +2.070e-07 and +6.389e-08; with the exact kappa_2, kappa_3 of D1-P10 in the refined equation they are +8.904e-08 and +1.443e-08. The verdict (survived, tolerances 2e-5 and 1.5e-5) is unchanged.

Formula-only predictor output used below (D1_fix_predict.py; kappa_2(51200) = 20.1459842829 and kappa_3(51200) = -8.721184 are the verifier's Taylor-DP values from D1_verify_ic_out_taylor_big.txt):
```
n=51200: g_n=16.786946491 x_2nd=16.777638486 xhat3=16.7784677362 xhat(k2 only)=16.7784668529
c_* = (log 2pi)/2 - 1/4 = 0.668939; c_*/log n at 51200 = 0.06169
```

**D1-P15 (Paper A comparison, own engine).** A new Markov engine (run-count closed form: the crossing solves 2 sum_k W_k u^k = 1 with u = (1-p)/p and W_k the number of words with h pluses, h minuses, first letter +, k switches; independent of both verifiers' DPs) gives:
(a) p_50 = 0.94200405, p_100 = 0.96496633, p_200 = 0.97939018, p_400 = 0.98812464 (Paper A table) to 1e-8.
(b) D(n) := x_n - (2 z_n - log 2 pi), z_n = n(1-p_n): D(3200) = +0.0479, D(12800) = +0.0642, D(25600) = +0.0658, each to within 2e-4 (verifier values).
(c) New cells: D(400) < D(800) < D(1600) < D(3200) and D(3200) < D(6400) < D(12800).
(d) Diagnosis of the wrong S11 numbers: replacing z_n by 2 x_B (x_B the Bessel root of 2x(I_0(2x)+I_1(2x)) = n/2, Paper A Thm "uniform Bessel approximation") gives D within 0.002 of the old values +0.038 (3200) and +0.061 (12800).
(e) New cell n = 51200 (heuristic extrapolation; the proved statement S11' only says D(n) = c_*/log n + O((log log n)^2/(log n)^2), c_* = 0.668939): D(51200) in [0.0635, 0.0680].
Kill: any failure of (a), (b), (c), (e). A failure of (d) only means the origin of the old numbers stays unexplained.

**D1-P16 (crossing at the new cell n = 51200; own forward window DP).**
(a) Proved for large n (S10(a)), not yet explicit at this n: x_51200 < g_51200 = 16.786946491.
(b) Heuristic (flat column (x_n - x_2nd) n/log n near 3.85-3.9): x_51200 - x_2nd in [0.00075, 0.00090], x_2nd = 16.777638486.
(c) Heuristic refined equation (S14(b)) with the verifier's exact kappa_2, kappa_3 at 51200: x_51200 = 16.7784677362 +- 2e-8.
(d) Proved one-sided S14(a): x_51200 <= xhat(kappa_2 only) + 1e-4 = 16.7785668529.
Kill: (a) or (d) fails (proof error or explicit-range issue); (b) or (c) fails (heuristic refuted).

**D1-P17 (repaired step in the proof of S6(b)).** At every feasible state (s,b), 1 <= b, 1 <= s-b, b <= h, s-b <= h, of the D1-P7b cells n in {40, 200, 1000}, eps in {0.001, 0.01, 0.05, 0.2}, with c = c_s, Sigma = s + 2c, z = (s-2b)^2/Sigma^2, W = z/(1-z), lambda = (Sigma/(Sigma+2kappa))^2, W' = lambda z/(1 - lambda z):
(a) W' <= lambda W, with strict inequality whenever s != 2b (so the old step "W' >= lambda W" is false);
(b) W' >= (1 - 2kappa/(1+c)) W >= (9/11) W;
(c) the corrected collected bound log D_s(b) <= kappa/Sigma + 2kappa/(3Sigma^2) + W [16kappa/(3s) - (9/11) beta_s], beta_s = 22kappa/(s(1+2gamma)), holds with log D_s(b) evaluated directly from Beta functions, and the bracket is < 0 at every state.
Kill: any violation beyond 1e-12 (relative for (a), (b); absolute for (c)).

**D1-P18 (derivation of the closed form for A_t^inf; exact rational check of the pre-limit identity).** For K ~ Bin(m, 1/2), u = m + t + 1, e_u = (u/2)(E[1/(1+K)] + E[1/(t+K)]) - 2 and, for every t >= 1 and M >= 0,
sum_{m=0}^{M} e_{m+t+1} = 2t H_{M+1} - sum_{m=0}^{M} (1 + t/(m+1)) 2^{-m} + [t>=2](1 - 2^{-M-1}) - (t-1) sum_{k=0}^{M} I(t-2, k+1) - t (H_{t-1} - sum_{j=0}^{t-2} I(j, M+1)),
with I(j,k) = int_0^1 x^j ((1+x)/2)^k dx = 2^{-k} sum_i C(k,i)/(i+j+1). Prediction: equality holds exactly (Fractions) for t = 1..8 and M = 0..40; e_u from the direct definition e_u = E[(u-2B)^2/(2B(u-B))], B = 1+K, also agrees exactly. The generating-function identity sum_{t>=1} t(t-2) 2^{-t-1} H_{t-1} = 2 + log 2 holds to 1e-30 (mpmath partial sums with the tail bounded).
Kill: any mismatch.

### Outcomes of batch 4 (2026-09-25; scripts D1_fix_crossing.py, D1_fix_markov.py, D1_fix_S6b.py, D1_fix_closedform.py; raw output D1_fix_out_crossing.txt, D1_fix_out_markov.txt, D1_fix_out_S6b.txt, D1_fix_out_closedform.txt)

Run order: D1_fix_S6b.py, D1_fix_crossing.py (background), D1_fix_markov.py, D1_fix_closedform.py. D1_fix_S6b.py was run twice: the first run printed the unscaled bracket under the label "max bracket*s/kappa"; the label was corrected and the identical computation rerun (same numbers).

```
== D1-P16 (D1_fix_out_crossing.txt) ==
n=25600: x_n=15.4672095164 (6.0s) log(C/E)=+0.00e+00
   g_n=15.481601406 g_n-x_n=0.014392 (x_n<g_n: True); x_2nd=15.465672221 x_n-x_2nd=0.001537 (x_n-x_2nd)n/log n=3.8772; x_n/log n=1.5238
   xhat3=15.4672095141 x_n-xhat3=+2.295e-09; xhat(k2 only)=15.4672065180 x_n-xhat=+2.998e-06 (S14(a): x_n <= xhat+1e-4: True)
n=51200: x_n=16.7784677365 (29.0s) log(C/E)=-6.04e-14
   g_n=16.786946491 g_n-x_n=0.008479 (x_n<g_n: True); x_2nd=16.777638486 x_n-x_2nd=0.000829 (x_n-x_2nd)n/log n=3.9155; x_n/log n=1.5473
   xhat3=16.7784677362 x_n-xhat3=+3.601e-10; xhat(k2 only)=16.7784668529 x_n-xhat=+8.837e-07 (S14(a): x_n <= xhat+1e-4: True)
== D1-P15 (D1_fix_out_markov.txt) ==
p_2 = 0.666666666667 (exact 2/3)
(a) N=50: p_N=0.9420040493 Paper A 0.94200405 diff=-7.28e-10 ok=True
(a) N=100: p_N=0.9649663263 Paper A 0.96496633 diff=-3.68e-09 ok=True
(a) N=200: p_N=0.9793901765 Paper A 0.97939018 diff=-3.49e-09 ok=True
(a) N=400: p_N=0.9881246429 Paper A 0.98812464 diff=+2.89e-09 ok=True
n=    50: z_n=2.89979754 x_n=3.9404868665 D=-0.02123 D*log n=-0.0831 c_*/log n=0.17100 | with z=2x_B (2.950785): -0.12321
n=   100: z_n=3.50336737 x_n=5.0958966738 D=-0.07296 D*log n=-0.3360 c_*/log n=0.14526 | with z=2x_B (3.543638): -0.15350
n=   200: z_n=4.12196470 x_n=6.3405901682 D=-0.06546 D*log n=-0.3468 c_*/log n=0.12625 | with z=2x_B (4.151514): -0.12456
n=   400: z_n=4.75014285 x_n=7.6292168962 D=-0.03319 D*log n=-0.1989 c_*/log n=0.11165 | with z=2x_B (4.770667): -0.07424
n=   800: z_n=5.38489648 x_n=8.9334617102 D=+0.00155 D*log n=+0.0103 c_*/log n=0.10007 | with z=2x_B (5.398565): -0.02579
n=  1600: z_n=6.02461808 x_n=10.2405649147 D=+0.02921 D*log n=+0.2155 c_*/log n=0.09067 | with z=2x_B (6.033425): +0.01159
n=  3200: z_n=6.66842332 x_n=11.5468344808 D=+0.04786 D*log n=+0.3863 c_*/log n=0.08288 | with z=2x_B (6.673949): +0.03681
n=  6400: z_n=7.31577269 x_n=12.8524830457 D=+0.05881 D*log n=+0.5155 c_*/log n=0.07633 | with z=2x_B (7.319166): +0.05203
n= 12800: z_n=7.96628194 x_n=14.1588452626 D=+0.06416 D*log n=+0.6068 c_*/log n=0.07073 | with z=2x_B (7.968328): +0.06007
n= 25600: z_n=8.61963702 x_n=15.4672095164 D=+0.06581 D*log n=+0.6680 c_*/log n=0.06590 | with z=2x_B (8.620853): +0.06338
n= 51200: z_n=9.27556054 x_n=16.7784677365 D=+0.06522 D*log n=+0.7073 c_*/log n=0.06169 | with z=2x_B (9.276273): +0.06380
(b) D(3200)=+0.04786 (pred +0.0479+-2e-4) ok=True; D(12800)=+0.06416 (pred +0.0642) ok=True
    D(25600)=+0.06581 (pred +0.0658) ok=True
(c) D(400)<D(800)<D(1600)<D(3200): True; D(3200)<D(6400)<D(12800): True
(e) D(51200)=+0.06522 in [0.0635,0.0680]: True
== D1-P17 (D1_fix_out_S6b.txt) ==
n=40 eps=0.001: states=399 nonsym=380 | (a) viol=0 strict W'<lamW at 380 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=9.726e-04 | (c) viol=0 max excess=-5.081e-05 max bracket=-6.503e-04 | ok=True
n=40 eps=0.01: states=399 nonsym=380 | (a) viol=0 strict W'<lamW at 380 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=7.714e-03 | (c) viol=0 max excess=-5.041e-04 max bracket=-6.574e-03 | ok=True
n=40 eps=0.05: states=399 nonsym=380 | (a) viol=0 strict W'<lamW at 380 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=1.797e-02 | (c) viol=0 max excess=-2.436e-03 max bracket=-3.483e-02 | ok=True
n=40 eps=0.2: states=399 nonsym=380 | (a) viol=0 strict W'<lamW at 380 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=7.211e-03 | (c) viol=0 max excess=-8.647e-03 max bracket=-2.803e-01 | ok=True
n=200 eps=0.001: states=9999 nonsym=9900 | (a) viol=0 strict W'<lamW at 9900 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=9.726e-04 | (c) viol=0 max excess=-1.003e-05 max bracket=-1.275e-04 | ok=True
n=200 eps=0.01: states=9999 nonsym=9900 | (a) viol=0 strict W'<lamW at 9900 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=6.126e-03 | (c) viol=0 max excess=-1.002e-04 max bracket=-1.288e-03 | ok=True
n=200 eps=0.05: states=9999 nonsym=9900 | (a) viol=0 strict W'<lamW at 9900 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=7.229e-03 | (c) viol=0 max excess=-4.974e-04 max bracket=-6.826e-03 | ok=True
n=200 eps=0.2: states=9999 nonsym=9900 | (a) viol=0 strict W'<lamW at 9900 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=1.862e-03 | (c) viol=0 max excess=-1.939e-03 max bracket=-5.494e-02 | ok=True
n=1000 eps=0.001: states=249999 nonsym=249500 | (a) viol=0 strict W'<lamW at 249500 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=9.726e-04 | (c) viol=0 max excess=-2.001e-06 max bracket=-2.539e-05 | ok=True
n=1000 eps=0.01: states=249999 nonsym=249500 | (a) viol=0 strict W'<lamW at 249500 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=1.751e-03 | (c) viol=0 max excess=-2.001e-05 max bracket=-2.566e-04 | ok=True
n=1000 eps=0.05: states=249999 nonsym=249500 | (a) viol=0 strict W'<lamW at 249500 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=1.567e-03 | (c) viol=0 max excess=-9.989e-05 max bracket=-1.360e-03 | ok=True
n=1000 eps=0.2: states=249999 nonsym=249500 | (a) viol=0 strict W'<lamW at 249500 | (b) viol=0 min(W'/W - (1-2k/(1+c)))=3.942e-04 | (c) viol=0 max excess=-3.975e-04 max bracket=-1.094e-02 | ok=True
ALL D1-P17 OK: True
== D1-P18 (D1_fix_out_closedform.txt) ==
t=1: M=0..40: e_direct==e_split fails=0; identity fails=0
t=2: M=0..40: e_direct==e_split fails=0; identity fails=0
t=3: M=0..40: e_direct==e_split fails=0; identity fails=0
t=4: M=0..40: e_direct==e_split fails=0; identity fails=0
t=5: M=0..40: e_direct==e_split fails=0; identity fails=0
t=6: M=0..40: e_direct==e_split fails=0; identity fails=0
t=7: M=0..40: e_direct==e_split fails=0; identity fails=0
t=8: M=0..40: e_direct==e_split fails=0; identity fails=0
ALL exact identities OK: True
sum t(t-2)2^(-t-1)H_(t-1) (t<600) = 2.693147180559945309417232121458176568076
2 + log 2                          = 2.693147180559945309417232121458176568076  diff=-1.7373e-50
K_2 series with closed-form A_t^inf = -1.53871585075687958820420794129; 2gamma_E-2-log2 = -1.53871585075687958820420794129
K_2/2 = gamma_E - 1 - (log 2)/2 = -0.76935792537844;  (1-gamma_E) + K_2/2 = -0.346573590279973 (= -(log 2)/2 = -0.346573590279973)
```

Verdicts: D1-P15 (a), (b), (c), (e) survive; (d) survives (with z = 2x_B the differences are +0.0368 at 3200 and +0.0601 at 12800, within 0.002 of the old +0.038 and +0.061, so the old S11 numbers were almost certainly computed from the Bessel root rather than the exact crossing). Note: D(n) is no longer increasing at the new cell (D(25600) = +0.06581, D(51200) = +0.06522), and D(n) log n = 0.707 at 51200 has passed c_* = 0.669; the approach to c_*/log n is slow and not monotone in D log n. D1-P16 (a)-(d) survive: x_51200 = 16.7784677365, refined-equation miss +3.6e-10 (tolerance 2e-8), x_n - x_2nd = 0.000829, column value 3.9155. x_25600 = 15.4672095164 reproduces both verifiers. D1-P17 survives in all 12 cells: W' < lambda W at every non-symmetric state (the old step is false), the repaired bound W' >= (1-2kappa/(1+c))W holds with positive margin, and the corrected collected bound holds with every bracket negative. D1-P18 survives: the pre-limit identity is exact for t = 1..8, M = 0..40, and the series identity holds to 1.7e-50.
