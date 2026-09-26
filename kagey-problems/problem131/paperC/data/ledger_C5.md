# Ledger C5: general second-order theory for face selection (Paper C). Predictions precede computations; outcomes appended verbatim.

Notation. Chain on d states with P_N = I + hQ, h = T/N, L = log N. For a face F (irreducible Q_F) with k = |F| states: lambda_F = Dirichlet exit rate, r,l = right/left Perron vectors of Q_F (l.r = 1), alpha*_F = l*r, Sigma_F = asymptotic covariance (any k-1 coordinates) of the occupation measure of the Doob transform R^{-1}(Q_F + lambda_F I)R, and
K_F = (mu.r)(l.1) (2 pi)^{-(k-1)/2} det(Sigma_F)^{-1/2}.
General prediction (Theorem X of C5.md): max over bins with support F of P_N(n) = N^{-(k-1)} K_F T^{(k-1)/2} e^{-T lambda_F} (1+o(1)); so for faces F, G with Delta = k_F - k_G > 0 and delta = lambda_G - lambda_F > 0 the modal crossing satisfies
Khat_N := Delta*L - (Delta/2) log T_N - delta*T_N -> log(K_F/K_G), with error O(1/L); equivalently T_N = (Delta/delta)[L - (1/2) log L + b_FG] + O(log L/L), b_FG = -(1/2) log(Delta/delta) - (1/Delta) log(K_F/K_G).
Predicted constants below come from C5_predict.py (theory only, run before any test).

## 2026-09-25 P0 (engine validation)
Prediction: the run-count engine (C5_engine.py: P_N(n) = sum_m W(m) h^{M-1} prod_i C(n_i-1,m_i-1)(1-h q_i)^{n_i-m_i}) agrees with a brute-force DP of the chain over all compositions, for N in {6,10,16,20}, (a) 4-cycle unit rates, h in {0.05, 0.2}; (b) a random non-reversible 4-state generator (seed 7, rates U(0.2,2)), h = 0.03; every bin with probability > 1e-250. The exact torus representation of the occupation density H(t) (Lemma R) agrees with the run-count sum for the random face at 5 random t.
Kill: any relative mismatch > 1e-8.

## 2026-09-25 P1 (requested cell: 4-cycle, vertex vs adjacent pair)
4-cycle, unit rates, uniform start. Vertex bin (N,0,0,0): (1/4)(1-2h)^{N-1}. Pair bin: balanced (ceil(N/2), floor(N/2), 0, 0).
Prediction (a), exact identity: the pair bin divided by the vertex bin equals Paper A's polynomial S_N(u) at u = h/(1-2h). Hence the crossing h*_N satisfies h*/(1-2h*) = u_N (Paper A's center root) exactly, for every N. Tested at N in {10, 40, 160, 640} against planar.py's uN (independent implementation of Paper A's formula).
Prediction (b): Delta = 1, delta = 1, K = log(K_pair/K_v) = log(4/sqrt(2 pi)) = 0.467355827915, b = (1/2) log(pi/8) = -0.467355827915 (the same constant as Paper A). With T_N = N h*_N, Khat_N = L - (1/2) log T_N - T_N -> 0.467355827915, at N = 10^3, ..., 10^12.
Kill: (a) relative mismatch > 1e-9 at any tested N; (b) |Khat_N - K| > 0.05 at N = 10^12, or |L (Khat_N - K)| changes by more than a factor 2 between N = 10^6 and 10^12.
Note written before running: (a) makes this cell degenerate (it is Paper A with an extra uniform killing), so P2 and P3 are the informative new cells.

## 2026-09-25 P2 (new cell: 4-cycle, adjacent pair vs full face)
Delta = 2, delta = 1, tau* = 2. K_full = 8/pi^{3/2} = 1.436696977001 (det Sigma = 1/512), K_pair = 1/sqrt(2 pi). Predicted K = log(8 sqrt 2/pi) = 1.281285246110, b = -0.987216213335, i.e. T_N = 2[L - (1/2) log L - 0.987216] + o(1).
M_pair = balanced pair bin; M_full = max over bins with all four counts positive, predicted to sit at (N/4,N/4,N/4,N/4) for 4 | N (to be checked by neighbour search).
Cells: N = 10^3, 10^4, ..., 10^8 (N divisible by 4).
Kill: fit Khat_N = K' + c/L + e/L^2 over the tested N gives |K' - 1.2813| > 0.03, or |Khat_N - K| at the largest N > 0.15, or the full-face max is not at the balanced bin.

## 2026-09-25 P3 (new cell: 4-cycle, vertex vs 3-arc face)
Delta = 2, delta = sqrt 2, tau* = sqrt 2 (never a global mode, but the modal crossing between the two faces is defined). alpha* = (1/4,1/2,1/4), K_arc = (4 + 3 sqrt 2)/(4 pi) = 0.655928504743, K_v = 1/4. Predicted K = 0.964590878470, b = -0.655582234375.
Khat_N = 2L - log T_N - sqrt2 T_N, M_arc = max over bins with support {0,1,2} (searched), N = 10^3, ..., 10^8.
Kill: as in P2 with 0.9646 in place of 1.2813.

## 2026-09-25 P4 (new cells: local law for a generic non-reversible face)
Random 4-state generator, seed 7, off-diagonal rates U(0.2,2); face F = {0,1,2} (killing to state 3), mu uniform. Also F = {0,1} and the full face.
Prediction: the continuum density f_T(alpha) (from the run-count sum, independent of the theory) divided by (T/2pi)^{(k-1)/2} C(alpha) e^{-T I(alpha)} tends to 1, with T(ratio - 1) converging, at alpha = alpha*_F and at two non-optimal interior alpha, for T in {10, 20, 40, 80, 160} (k = 2, 3) and T up to 40 (k = 4).
Kill: ratio at the largest T outside [0.97, 1.03], or |T(ratio-1)| changing by more than 30% between the two largest T.

## 2026-09-25 P5 (discrete vs continuum)
Same chain, F = {0,1,2}, T = 10, n = round(N alpha*): P_N(n) / (N^{-2} f_T(n/N)) - 1 = O(T^2/N): N(ratio-1)/T^2 stays bounded for N in {10^3, 10^4, 10^5, 10^6}.
Kill: |ratio - 1| > 1e-3 at N = 10^6, or N|ratio-1|/T^2 varying by more than a factor 3 over the four N.

## 2026-09-25 P6 (possibly new: an intermediate face wins in the window under a non-uniform start)
K_3 (Paper B, d = 3), unit rates, start mu = (1/2, 1/2, 0). Window Nu = L - (1/2) log L + t with u = h/(1-2h).
Limit lines (general theory): vertex 1 or 2: log(1/2) - 2t; edge {1,2}: log(K_e) - t with K_e = 2^{3/2}/sqrt(4 pi) = 0.797885; full: log(D_3/3) = log 1.240490 (flat). Other faces are lower.
Prediction: the balanced edge bin is the unique global mode for t in (-0.467356, -0.441306) in the limit; at the midpoint t = -0.4543 and N = 10^14 the edge-center bin exceeds the vertex bin and the full-face maximum (searched) by log-margins near +0.013 each; finite-N crossing values t_ve(N) -> -0.467356 and t_ef(N) -> -0.441306.
Kill: at N = 10^14 and t = -0.4543 the edge bin is not strictly the largest of the three face maxima, or the measured t_ve, t_ef at N = 10^14 are further than 0.02 from the predicted limits.

### P0 outcome (C5_P0_validate.py, verbatim output)
```
4-cycle N=6 h=0.05: bins=74 max rel err=1.221e-15
4-cycle N=6 h=0.2: bins=74 max rel err=1.110e-15
4-cycle N=10 h=0.05: bins=268 max rel err=2.109e-15
4-cycle N=10 h=0.2: bins=268 max rel err=2.220e-15
4-cycle N=16 h=0.05: bins=939 max rel err=2.442e-15
4-cycle N=16 h=0.2: bins=939 max rel err=3.553e-15
4-cycle N=20 h=0.05: bins=1733 max rel err=4.441e-15
4-cycle N=20 h=0.2: bins=1733 max rel err=6.883e-15
random generator (seed 7):
 [[-4.0166  1.815   1.5962  0.6054]
 [ 0.7403 -2.628   0.2095  1.6782]
 [ 1.6347  1.0423 -3.3782  0.7012]
 [ 0.6588  1.0011  1.1082 -2.7681]]
random  N=6 h=0.03: bins=84 max rel err=2.554e-15
random  N=10 h=0.03: bins=286 max rel err=3.331e-15
random  N=16 h=0.03: bins=969 max rel err=3.775e-15
random  N=20 h=0.03: bins=1771 max rel err=5.773e-15
  t=[1.485 3.223 9.715]  log H torus=20.459046552751  run-sum=20.459046552751  rel diff=5.79e-13
  t=[7.195 1.582 5.481]  log H torus=28.666204942278  run-sum=28.666204942278  rel diff=3.16e-13
  t=[6.009 2.337 8.948]  log H torus=34.207438006854  run-sum=34.207438006854  rel diff=3.55e-14
  t=[1.807 4.999 6.443]  log H torus=21.035024975793  run-sum=21.035024975793  rel diff=0.00e+00
  t=[5.452 7.248 8.985]  log H torus=41.930610398113  run-sum=41.930610398113  rel diff=1.42e-14
```
Verdict: P0 survives (max engine/brute mismatch 6.9e-15; torus vs run-sum 5.8e-13).

### P4 outcome (C5_P4_local.py, verbatim output)
Ratio = exact density (torus representation, validated against the independent run-count sum wherever the run-sum truncation is < 1e-13; "nan" marks cells where only the torus value is available) divided by the predicted local law.
```
Face [0, 1]: k=2 lambda_F=1.9711100519 alpha*=[0.243076 0.756924] K_F=0.5258449204
  alpha=[0.2431 0.7569] I=1.9711100519 C=0.5258449204  (pi check 2.8e-17)
    T=  10  ratio torus/pred=0.9864431370  T(ratio-1)=-0.135569  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9932950589  T(ratio-1)=-0.134099  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  40  ratio torus/pred=0.9966648763  T(ratio-1)=-0.133405  run-sum vs torus rel=1.4e-14 (trunc 0.0e+00)
    T=  80  ratio torus/pred=0.9983366614  T(ratio-1)=-0.133067  run-sum vs torus rel=2.8e-14 (trunc 0.0e+00)
    T= 160  ratio torus/pred=0.9991693731  T(ratio-1)=-0.132900  run-sum vs torus rel=5.7e-14 (trunc 0.0e+00)
  alpha=[0.3 0.7] I=1.9821893863 C=0.4920175795  (pi check 1.1e-16)
    T=  10  ratio torus/pred=0.9881366862  T(ratio-1)=-0.118633  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9941242788  T(ratio-1)=-0.117514  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  40  ratio torus/pred=0.9970754457  T(ratio-1)=-0.116982  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  80  ratio torus/pred=0.9985409732  T(ratio-1)=-0.116722  run-sum vs torus rel=2.8e-14 (trunc 0.0e+00)
    T= 160  ratio torus/pred=0.9992712901  T(ratio-1)=-0.116594  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
  alpha=[0.8 0.2] I=2.8115500820 C=0.5647853865  (pi check 1.1e-16)
    T=  10  ratio torus/pred=0.9844561836  T(ratio-1)=-0.155438  run-sum vs torus rel=-3.6e-15 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9923246477  T(ratio-1)=-0.153507  run-sum vs torus rel=7.1e-15 (trunc 0.0e+00)
    T=  40  ratio torus/pred=0.9961849240  T(ratio-1)=-0.152603  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  80  ratio torus/pred=0.9980979449  T(ratio-1)=-0.152164  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T= 160  ratio torus/pred=0.9990503235  T(ratio-1)=-0.151948  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
Face [0, 1, 2]: k=3 lambda_F=1.1614504843 alpha*=[0.316032 0.387635 0.296333] K_F=1.0423613241
  alpha=[0.316  0.3876 0.2963] I=1.1614504843 C=1.0423613244  (pi check 2.7e-09)
    T=  10  ratio torus/pred=0.9764513963  T(ratio-1)=-0.235486  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9882822300  T(ratio-1)=-0.234355  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  40  ratio torus/pred=0.9941544748  T(ratio-1)=-0.233821  run-sum vs torus rel=2.8e-14 (trunc 0.0e+00)
    T=  80  ratio torus/pred=0.9970804903  T(ratio-1)=-0.233561  run-sum vs torus rel=-2.8e-14 (trunc 0.0e+00)
    T= 160  ratio torus/pred=0.9985410480  T(ratio-1)=-0.233432  run-sum vs torus rel=nan (trunc 2.0e-02)
  alpha=[0.2 0.5 0.3] I=1.2334838623 C=1.1219835343  (pi check 1.0e-11)
    T=  10  ratio torus/pred=0.9744947407  T(ratio-1)=-0.255053  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9873051065  T(ratio-1)=-0.253898  run-sum vs torus rel=-7.1e-15 (trunc 0.0e+00)
    T=  40  ratio torus/pred=0.9936661695  T(ratio-1)=-0.253353  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  80  ratio torus/pred=0.9968363973  T(ratio-1)=-0.253088  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T= 160  ratio torus/pred=0.9984190159  T(ratio-1)=-0.252957  run-sum vs torus rel=nan (trunc 7.0e-07)
  alpha=[0.6  0.25 0.15] I=1.5179638445 C=1.4300056192  (pi check 1.3e-09)
    T=  10  ratio torus/pred=0.9702775422  T(ratio-1)=-0.297225  run-sum vs torus rel=0.0e+00 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9852441057  T(ratio-1)=-0.295118  run-sum vs torus rel=-7.1e-15 (trunc 0.0e+00)
    T=  40  ratio torus/pred=0.9926466172  T(ratio-1)=-0.294135  run-sum vs torus rel=2.8e-14 (trunc 0.0e+00)
    T=  80  ratio torus/pred=0.9963292542  T(ratio-1)=-0.293660  run-sum vs torus rel=2.8e-14 (trunc 0.0e+00)
    T= 160  ratio torus/pred=0.9981660893  T(ratio-1)=-0.293426  run-sum vs torus rel=nan (trunc 7.2e-02)
Face [0, 1, 2, 3]: k=4 lambda_F=0.0000000000 alpha*=[0.188941 0.320538 0.203356 0.287165] K_F=3.3251427151
  alpha=[0.1889 0.3205 0.2034 0.2872] I=0.0000000000 C=3.3251427151  (pi check 1.1e-16)
    T=  10  ratio torus/pred=0.9639568515  T(ratio-1)=-0.360431  run-sum vs torus rel=-2.0e-13 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9819782128  T(ratio-1)=-0.360436  run-sum vs torus rel=nan (trunc 4.5e-09)
    T=  40  ratio torus/pred=0.9909912681  T(ratio-1)=-0.360349  run-sum vs torus rel=nan (trunc 3.8e-01)
  alpha=[0.4  0.2  0.25 0.15] I=0.3033842390 C=3.7024044115  (pi check 1.1e-10)
    T=  10  ratio torus/pred=0.9610936694  T(ratio-1)=-0.389063  run-sum vs torus rel=3.6e-15 (trunc 0.0e+00)
    T=  20  ratio torus/pred=0.9805580646  T(ratio-1)=-0.388839  run-sum vs torus rel=nan (trunc 3.4e-06)
    T=  40  ratio torus/pred=0.9902810655  T(ratio-1)=-0.388757  run-sum vs torus rel=nan (trunc 7.9e-01)
```
Verdict: P4 survives. All ratios at the largest T lie in [0.9982, 0.9992] (k = 2, 3) and 0.9903 to 0.9910 (k = 4, T = 40); T(ratio-1) changes by < 0.3% between the two largest T in every row, so the correction is c(alpha)/T with c(alpha) in [-0.39, -0.12].

### P5 outcome (C5_P5_discrete.py, verbatim output, after the stable-binomial fix below)
```
face {0,1,2}, T=10, n = round(N alpha*)
  N=    1000 n=[316 388 296]  P_N(n)=8.9497699902e-11  ratio=0.973198107997  N(ratio-1)/T^2=-0.268019
  N=   10000 n=[3160 3877 2963]  P_N(n)=9.1702742899e-13  ratio=0.997291294722  N(ratio-1)/T^2=-0.270871
  N=  100000 n=[31603 38764 29633]  P_N(n)=9.1925569689e-15  ratio=0.999728847779  N(ratio-1)/T^2=-0.271152
  N= 1000000 n=[316032 387636 296332]  P_N(n)=9.1947920839e-17  ratio=0.999972881956  N(ratio-1)/T^2=-0.271180
```
Verdict: P5 survives (N(ratio-1)/T^2 -> -0.27118; |ratio-1| = 2.7e-5 at N = 1e6).

### P1 outcome (C5_P1_cycle_pair.py, verbatim output)
Engine note: a first run used gammaln differences for log C(n-1,m-1), which lose about 1e-3 absolute accuracy at n ~ 1e12 (L(Khat-K) read -0.1430, -0.1508 at N = 1e11, 1e12). The binomial is now computed as sum_j log(n-j) - log(m-1)!; P0 and P5 were rerun and are unchanged to 1e-14. Output of the corrected run:
```
(a) identity h*/(1-2h*) = Paper A u_N
  N=  10  u(4-cycle)=0.192742240476221  u_N(Paper A)=0.192742240476011  rel diff=+1.09e-12  pointwise log-ratio diff=+8.88e-16
  N=  40  u(4-cycle)=0.072675771725680  u_N(Paper A)=0.072675771725733  rel diff=-7.31e-13  pointwise log-ratio diff=-6.66e-16
  N= 160  u(4-cycle)=0.025125664171332  u_N(Paper A)=0.025125664171502  rel diff=-6.79e-12  pointwise log-ratio diff=+5.57e-14
  N= 640  u(4-cycle)=0.008159716092024  u_N(Paper A)=0.008159716092042  rel diff=-2.18e-12  pointwise log-ratio diff=+2.66e-15
(b) Khat_N = L - (1/2)log T_N - T_N, predicted limit K = 0.467355827915
  N=1e3  T_N=5.5592728793  Khat=0.4907487383  Khat-K=+2.339e-02  L(Khat-K)=+0.161593  pred T=L-(1/2)logL+b: 5.474077
  N=1e4  T_N=7.7282882517  Khat=0.4596084224  Khat-K=-7.747e-03  L(Khat-K)=-0.071356  pred T=L-(1/2)logL+b: 7.632821
  N=1e5  T_N=9.9102606532  Khat=0.4558794868  Khat-K=-1.148e-02  L(Khat-K)=-0.132126  pred T=L-(1/2)logL+b: 9.823834
  N=1e6  T_N=12.1114057617  Khat=0.4570309795  Khat-K=-1.032e-02  L(Khat-K)=-0.142643  pred T=L-(1/2)logL+b: 12.035259
  N=1e7  T_N=14.3284676454  Khat=0.4585038542  Khat-K=-8.852e-03  L(Khat-K)=-0.142677  pred T=L-(1/2)logL+b: 14.260769
  N=1e8  T_N=16.5575668898  Khat=0.4596922486  Khat-K=-7.664e-03  L(Khat-K)=-0.141168  pred T=L-(1/2)logL+b: 16.496588
  N=1e9  T_N=18.7958336369  Khat=0.4606145849  Khat-K=-6.741e-03  L(Khat-K)=-0.139701  pred T=L-(1/2)logL+b: 18.740281
  N=1e10 T_N=21.0412656164  Khat=0.4613425441  Khat-K=-6.013e-03  L(Khat-K)=-0.138461  pred T=L-(1/2)logL+b: 20.990186
  N=1e11 T_N=23.2924413923  Khat=0.4619301786  Khat-K=-5.426e-03  L(Khat-K)=-0.137423  pred T=L-(1/2)logL+b: 23.245116
  N=1e12 T_N=25.5483211889  Khat=0.4624141232  Khat-K=-4.942e-03  L(Khat-K)=-0.136544  pred T=L-(1/2)logL+b: 25.504196
```
Verdict: P1 survives. (a) identity holds to 7e-12 (root tolerance). (b) |Khat-K| = 4.9e-3 at N = 1e12; L(Khat-K) moves from -0.1426 (1e6) to -0.1365 (1e12), consistent with Paper A's own 1/(8z) term (L(Khat-K) -> -1/8).

### P3 outcome (C5_P23_cycle.py P3, verbatim output)
```
P3: vertex vs 3-arc, predicted K = 0.964590878470
  N=1e3  T_N=7.5985718035  Khat=1.0415469498  Khat-K=+7.6956e-02  L(Khat-K)=+0.53159  mode a/N=0.228678 (alpha*=0.25)  2D-sym=-3.6e-14  lattice-real=-6.2e-06  pred T=7.47532
  N=1e4  T_N=10.6701277154  Khat=0.9633933817  Khat-K=-1.1975e-03  L(Khat-K)=-0.01103  mode a/N=0.235114 (alpha*=0.25)  2D-sym=-5.7e-14  lattice-real=-2.2e-08  pred T=10.52825
  N=1e5  T_N=13.7557035794  Khat=0.9508948241  Khat-K=-1.3696e-02  L(Khat-K)=-0.15768  mode a/N=0.238647 (alpha*=0.25)  2D-sym=+2.1e-14  lattice-real=-1.3e-09  pred T=13.62681
  N=1e6  T_N=16.8676570402  Khat=0.9511537605  Khat-K=-1.3437e-02  L(Khat-K)=-0.18564  mode a/N=0.240850 (alpha*=0.25)  2D-sym=+2.8e-14  lattice-real=-1.5e-11  pred T=16.75423
  N=1e7  T_N=20.0022303954  Khat=0.9529220119  Khat-K=-1.1669e-02  L(Khat-K)=-0.18808  mode a/N=0.242347 (alpha*=0.25)  2D-sym=+2.8e-14  lattice-real=-1.4e-13  pred T=19.90158
  N=1e8  T_N=23.1540123779  Khat=0.9544750733  Khat-K=-1.0116e-02  L(Khat-K)=-0.18634  mode a/N=0.243429 (alpha*=0.25)  2D-sym=+4.3e-14  lattice-real=-5.7e-14  pred T=23.06351
  fit Khat = K' + c/L + e/L^2: K'=1.066760 c=-3.1072 e=+20.2054  (predicted K=0.964591)
  same fit on N>=1e5 only: K'=0.982841
```
Verdict: P3 is KILLED by the letter of its pre-registered fit criterion: the fit K' + c/L + e/L^2 over all tested N gives K' = 1.066760, |K' - 0.9646| = 0.102 > 0.03. The other criterion passes (|Khat - K| = 0.0101 < 0.15 at N = 1e8). Diagnosis, written after seeing the output: the three-parameter fit is dominated by N = 1e3 and 1e4, where T^2/N = 0.058 and 0.011 and the model omits log L/L^2 terms; L(Khat - K) is flat (-0.1856, -0.1881, -0.1863) for N = 1e6..1e8, which is what a correct K with an O(1/L) correction produces. The kill stands as recorded; the criterion was badly designed. A corrected, independent test (P3') is registered below before running.
Mode location: symmetric (2D search agrees to 4e-14), a/N = 0.2434 at N = 1e8, drifting to alpha*_0 = 1/4 at rate O(1/T) as the theory predicts.

## 2026-09-25 P3' (new cells: 4-cycle vertex vs 3-arc, N = 1e9 ... 1e14)
Prediction: Khat_N -> K = 0.964590878470 with Khat_N - K = c/L + O(log L/L^2). Concretely: (i) L(Khat_N - K) lies in [-0.24, -0.13] for every N in {1e9, 1e10, ..., 1e14}; (ii) a fit Khat = K' + c/L + e/L^2 on N in {1e6, ..., 1e14} gives |K' - K| < 0.02; (iii) |Khat - K| < 0.012 at N = 1e14.
Kill: any of (i)-(iii) fails.
Alternative I am testing against: if the constant were wrong by an amount D, L(Khat - K) would drift linearly in L by D per unit L; over L = 20.7..32.2 this moves it by 11.5 D.

## 2026-09-25 P2 addendum (registered before P2 is run; the original P2 criterion is kept unchanged)
Additional criteria: L(Khat_N - K) varies by less than 30% over N = 1e6, 1e7, 1e8; the fit on N >= 1e5 has |K' - 1.2813| < 0.03.

### P2 outcome (C5_P23_cycle.py P2, verbatim output)
```
P2: pair vs full, predicted K = 1.281285246110
  N=1e3  T_N=10.2024335653  Khat=1.2904507160  Khat-K=+9.1655e-03  L(Khat-K)=+0.06331  max neighbour log-diff=-3.266e-05  trunc=0.0e+00  pred T=9.90843
  N=1e4  T_N=14.4863218829  Khat=1.2611539752  Khat-K=-2.0131e-02  L(Khat-K)=-0.18542  max neighbour log-diff=-4.933e-07  trunc=0.0e+00  pred T=14.22592
  N=1e5  T_N=18.8308173446  Khat=1.2595388371  Khat-K=-2.1746e-02  L(Khat-K)=-0.25036  max neighbour log-diff=-6.656e-09  trunc=0.0e+00  pred T=18.60795
  N=1e6  T_N=23.2233383709  Khat=1.2625250077  Khat-K=-1.8760e-02  L(Khat-K)=-0.25918  max neighbour log-diff=-8.407e-11  trunc=0.0e+00  pred T=23.03080
  N=1e7  T_N=27.6511571571  Khat=1.2653665675  Khat-K=-1.5919e-02  L(Khat-K)=-0.25658  max neighbour log-diff=-1.009e-12  trunc=0.0e+00  pred T=27.48182
  N=1e8  T_N=32.1047928207  Khat=1.2675633392  Khat-K=-1.3722e-02  L(Khat-K)=-0.25277  max neighbour log-diff=-1.421e-14  trunc=3.2e-12  pred T=31.95346
  fit Khat = K' + c/L + e/L^2: K'=1.330405 c=-1.6406 e=+9.4004  (predicted K=1.281285)
  same fit on N>=1e5 only: K'=1.290586
```
Verdict: the ORIGINAL P2 criterion is triggered (all-N fit K' = 1.330405, |K' - 1.2813| = 0.049 > 0.03), so P2 is killed as written; |Khat - K| = 0.0137 < 0.15 at N = 1e8 passes. The addendum criteria (registered before the run) pass: L(Khat-K) = -0.2592, -0.2566, -0.2528 over N = 1e6..1e8 (2.5% spread), fit on N >= 1e5 gives K' = 1.290586 (|diff| = 0.0093). The balanced bin (N/4,N/4,N/4,N/4) is the full-face maximum at every tested crossing (all 12 neighbours lower). Same diagnosis as P3: the all-N fit is driven by N = 1e3, 1e4.

### P3' outcome (C5_P23_cycle.py P3 ext, verbatim output; a first run saved as C5_P3ext_out.txt, re-run on 2026-09-25 as C5_P3ext_rerun_out.txt, byte-identical)
```
P3: vertex vs 3-arc, predicted K = 0.964590878470
  N=1e6  T_N=16.8676570402  Khat=0.9511537605  Khat-K=-1.3437e-02  L(Khat-K)=-0.18564  mode a/N=0.240850 (alpha*=0.25)  2D-sym=+2.8e-14  lattice-real=-1.5e-11  pred T=16.75423
  N=1e7  T_N=20.0022303954  Khat=0.9529220119  Khat-K=-1.1669e-02  L(Khat-K)=-0.18808  mode a/N=0.242347 (alpha*=0.25)  2D-sym=+2.8e-14  lattice-real=-1.4e-13  pred T=19.90158
  N=1e8  T_N=23.1540123779  Khat=0.9544750733  Khat-K=-1.0116e-02  L(Khat-K)=-0.18634  mode a/N=0.243429 (alpha*=0.25)  2D-sym=+4.3e-14  lattice-real=-5.7e-14  pred T=23.06351
  N=1e9  T_N=26.3189021685  Khat=0.9556958857  Khat-K=-8.8950e-03  L(Khat-K)=-0.18433  mode a/N=0.244246 (alpha*=0.25)  2D-sym=+5.7e-14  lattice-real=+0.0e+00  pred T=26.23657
  N=1e10  T_N=29.4940274523  Khat=0.9566604442  Khat-K=-7.9304e-03  L(Khat-K)=-0.18260  mode a/N=0.244884 (alpha*=0.25)  2D-sym=+1.4e-14  lattice-real=-1.4e-14  pred T=29.41841
  N=1e11  T_N=32.6773498696  Khat=0.9574385046  Khat-K=-7.1524e-03  L(Khat-K)=-0.18116  mode a/N=0.245396 (alpha*=0.25)  2D-sym=+5.7e-14  lattice-real=+1.4e-14  pred T=32.60737
  N=1e12  T_N=35.8673800013  Khat=0.9580787399  Khat-K=-6.5121e-03  L(Khat-K)=-0.17994  mode a/N=0.245815 (alpha*=0.25)  2D-sym=+2.0e-13  lattice-real=+5.7e-14  pred T=35.80219
  N=1e13  T_N=39.0629984173  Khat=0.9586145822  Khat-K=-5.9763e-03  L(Khat-K)=-0.17889  mode a/N=0.246165 (alpha*=0.25)  2D-sym=+3.4e-13  lattice-real=+3.1e-13  pred T=39.00194
  N=1e14  T_N=42.2633430681  Khat=0.9590695295  Khat-K=-5.5213e-03  L(Khat-K)=-0.17799  mode a/N=0.246462 (alpha*=0.25)  2D-sym=+5.7e-14  lattice-real=-8.5e-14  pred T=42.20588
  fit Khat = K' + c/L + e/L^2: K'=0.965721 c=-0.2212 e=+0.2658  (predicted K=0.964591)
```
Verdict: P3' survives. (i) L(Khat-K) for N = 1e9..1e14 is -0.18433, -0.18260, -0.18116, -0.17994, -0.17889, -0.17799, all in [-0.24, -0.13]. (ii) the fit on N = 1e6..1e14 gives K' = 0.965721, |K' - K| = 0.00113 < 0.02. (iii) |Khat - K| = 5.52e-3 < 0.012 at N = 1e14. Remark written after the run: T_N(Khat_N - K) = -0.2339, -0.2336, -0.2333 at N = 1e10, 1e12, 1e14, so the residual is a clean c/T term with c close to -0.232 (tested independently in P7 below).

## 2026-09-25 P7 (new cells: the O(1/T) coefficient of continuum face maxima, a third-order consistency test)
Registered after P1, P2, P3' outcomes were seen and before any of the computations below.
Definition. c_F := lim_{T->oo} T [ Mc_F(T) / (T^{(k-1)/2} K_F e^{-T lambda_F}) - 1 ], where Mc_F(T) = max over the open face simplex of the continuum density f_T(alpha). By Theorem L of C5.md (full Laplace expansion) and the discrete-continuum Lemma D, the crossing residual satisfies T_N (Khat_N - K) -> c_F - c_G; the vertex face has c = 0.
Predictions: (a) 4-cycle pair (= Paper A with uniform killing): c = -1/8 (Paper A's 1/(8z) term). (b) complete graph K_3, full face, uniform mu: c = -1/4 (Paper B's k-independent 1/(8z) term gives c = -(k-1)/8). (c) 4-cycle 3-arc: c in [-0.236, -0.228] (extrapolated from P3': T_N(Khat-K) = -0.2339, -0.2336, -0.2333 at N = 1e10, 1e12, 1e14). (d) 4-cycle full face: c in [-0.58, -0.55] (from P2: T_N(Khat-K) = -0.4357, -0.4402, -0.4405 at N = 1e6..1e8, plus c_pair = -0.125).
Method: exact torus representation of f_T (Lemma R), trapezoidal rule, maximisation over alpha on the symmetric subspace (a symmetric maximiser is forced by symmetry for (a), (b), (d); for (c) a 1-D search on alpha_1 = alpha_3), T in {25, 50, 100, 200} (and 400 where affordable), Richardson extrapolation in 1/T.
Kill: |c_pair + 0.125| > 0.003, or |c_K3 + 0.25| > 0.005, or c_arc outside [-0.236, -0.228], or c_full outside [-0.58, -0.55].

## 2026-09-25 P8 (identities behind the constant; random instances, not tested before)
(a) Legendre: det Sigma_alpha * det Hess I(alpha) = 1 (Hessian in the coordinates alpha_2..alpha_k), for random faces (k = 2..5, random non-reversible rates) at random interior alpha. Hessian by 4th-order central differences of I computed by convex minimisation. Kill: relative mismatch > 1e-5 (finite-difference limited).
(b) Reversible faces (a_ij = s_ij / nu_i with s symmetric, nu > 0 random): det Sigma_alpha = 2^{k-1} (prod alpha_i)^2 / tau(c), tau = weighted spanning-tree count (matrix-tree theorem) with conductances c_ij = sqrt(alpha_i alpha_j) s_ij / sqrt(nu_i nu_j); also r = sqrt(alpha/nu), l = sqrt(alpha nu) and I(alpha) = sum q_i alpha_i - sum_{i != j} c_ij. Kill: relative mismatch > 1e-9.
(c) Non-reversible faces: with c_ij = (l_i a_ij r_j + l_j a_ji r_i)/2 (additive reversiblisation of the Doob transform), det Sigma_alpha <= 2^{k-1} (prod alpha_i)^2 / tau(c), strictly for generic random rates. Kill: any instance with det Sigma > (1 + 1e-9) * bound, or equality to 1e-6 on a generic non-reversible instance.

## 2026-09-25 P9 (new cell: 4-cycle 3-arc vs adjacent pair; both faces non-trivial, Delta = 1)
delta = sqrt2 - 1 = 0.414213562373, tau* = 2.4142135624 (a face-maxima crossing, not a global-mode transition). Predicted K = log(K_arc/K_pair) = 0.497235050554, b = -0.937921844064.
Khat_N = L - (1/2) log T_N - delta T_N with T_N the root of M_arc = M_pair (M_pair at the balanced pair bin, M_arc searched as in P3), N = 1e4, 1e6, 1e8, 1e10, 1e12.
Predictions: |Khat_N - K| < 0.01 at N = 1e12; T_N (Khat_N - K) at N = 1e12 lies in [-0.13, -0.085] (c_arc - c_pair with c_arc ~ -0.232, c_pair = -0.125).
Kill: either fails.

## 2026-09-25 P10 (new cell: non-reversible face, non-symmetric maximiser)
Random 4-state generator (seed 7, as in P0/P4), uniform start. F = {0,1,2} (k = 3, lambda_F = 1.1614504843, K_F = 1.0423613241, non-reversible), G = {0,1} (k = 2, lambda_G = 1.9711100519, K_G = 0.5258449204). Delta = 1, delta = 0.8096595676, tau* = 1.2350869921. Predicted K = log(K_F/K_G) = 0.6842375812, b = -0.7898082845.
M_F = max over bins with support F (2-D search over real n, then lattice check), M_G = max over bins with support G (1-D search), N = 1e4, 1e6, 1e8, 1e10, 1e12; Khat_N = L - (1/2) log T_N - delta T_N.
Predictions: |Khat_N - K| < 0.03 at N = 1e12; |T_N (Khat_N - K)| < 1 and it changes by less than 0.05 between N = 1e10 and 1e12.
Kill: any fails.

### P6 outcome (C5_P6_window.py, verbatim output)
```
engine vs brute force (K_3, mu=(1/2,1/2,0)), max rel err = 3.11e-15
N=1e6  T(t=-0.4543)=12.0480  t_ve=-0.390915 (lim -0.467356)  t_ef=-0.369274 (lim -0.441306)  t_fv=-0.380097 (lim -0.454339)
      at t=-0.4543: edge-vertex=-0.066064  edge-full=+0.088588  edge-edge02=+0.682560  [full argmax n2/N=0.323540, 2D-1D=+7.1e-15, lattice-real=-6.5e-13, trunc=0.0e+00, edge nbr-center=-2.2e-11]
N=1e8  T(t=-0.4543)=16.5096  t_ve=-0.406371 (lim -0.467356)  t_ef=-0.383638 (lim -0.441306)  t_fv=-0.395006 (lim -0.454339)
      at t=-0.4543: edge-vertex=-0.049401  edge-full=+0.072818  edge-edge02=+0.685462  [full argmax n2/N=0.326303, 2D-1D=+1.4e-14, lattice-real=-4.3e-14, trunc=0.0e+00, edge nbr-center=+7.1e-15]
N=1e10  T(t=-0.4543)=21.0032  t_ve=-0.416276 (lim -0.467356)  t_ef=-0.392833 (lim -0.441306)  t_fv=-0.404555 (lim -0.454339)
      at t=-0.4543: edge-vertex=-0.038939  edge-full=+0.062940  edge-edge02=+0.687125  [full argmax n2/N=0.327859, 2D-1D=+1.3e-13, lattice-real=+1.3e-13, trunc=0.0e+00, edge nbr-center=+0.0e+00]
N=1e12  T(t=-0.4543)=25.5173  t_ve=-0.423230 (lim -0.467356)  t_ef=-0.399323 (lim -0.441306)  t_fv=-0.411277 (lim -0.454339)
      at t=-0.4543: edge-vertex=-0.031684  edge-full=+0.056060  edge-edge02=+0.688201  [full argmax n2/N=0.328855, 2D-1D=+1.4e-13, lattice-real=-1.4e-14, trunc=0.0e+00, edge nbr-center=-1.4e-14]
N=1e14  T(t=-0.4543)=30.0453  t_ve=-0.428404 (lim -0.467356)  t_ef=-0.404171 (lim -0.441306)  t_fv=-0.416288 (lim -0.454339)
      at t=-0.4543: edge-vertex=-0.026331  edge-full=+0.050967  edge-edge02=+0.688952  [full argmax n2/N=0.329546, 2D-1D=+1.7e-13, lattice-real=+0.0e+00, trunc=0.0e+00, edge nbr-center=+5.7e-14]
```
Verdict: P6 is KILLED. At N = 1e14 and t = -0.4543 the edge bin is below the vertex bin (edge - vertex = -0.026331), and the measured crossings t_ve = -0.428404, t_ef = -0.404171 are 0.0390 and 0.0371 from the predicted limits, both beyond the 0.02 tolerance.
Diagnosis (written after seeing the output). The limits -0.467356 and -0.441306 are the N -> oo values; the prediction ignored the deterministic drift of the window coordinate. With T = L - (1/2) log L + t, the term (1/2) log T - (1/2) log L equals -(log L)/(4L) + t/(2L) + O((log L)^2/L^2), which is Paper B's own ((1/4) log L - a_k/2 + 1/8)/L correction and is 0.038 at N = 1e14. Solving the second-order equation T + (1/2) log T = L - log(K_e/K_v) + 1/(8T) exactly (no fitted parameter) gives t = -0.428448 at N = 1e14 against the measured -0.428404. The window itself exists at every tested N: the edge beats both vertex and full face for t in (t_ve, t_ef), of width 0.021641, 0.022733, 0.023443, 0.023907, 0.024233 at N = 1e6, ..., 1e14 (limit 0.026050). (Widths recomputed from the printed t_ve, t_ef; an earlier draft of this sentence had transcription errors and was corrected within the same session.) The fixed-t test was placed outside the finite-N window. The kill stands; a corrected test on new cells is registered as P6'.

## 2026-09-25 P6' (new cells N = 1e16, 1e18, 1e20; corrected version of P6, registered after P6 was killed)
Same model and code as P6 (K_3, unit rates, mu = (1/2, 1/2, 0), window T = L - (1/2) log L + t via u).
Predictions: (i) |t_ve(N) - that_ve(N)| < 5e-4, where that_ve(N) is the root t of T + (1/2) log T = L - log(K_e/K_v) + 1/(8T), T = L - (1/2) log L + t, log(K_e/K_v) = 0.467355827915 (no fitted parameter; the 1/(8T) is Paper A's term, c_pair = -1/8). (ii) the edge window is nonempty with width t_ef(N) - t_ve(N) in [0.0240, 0.0261] at each of the three N, and increasing in N. (iii) the edge beats vertex, both other edges and the full face at the measured window midpoint (trivial given (ii); reported for completeness).
Kill: (i) or (ii) fails at any of the three N.

### P6' outcome (C5_P6prime.py, verbatim output of the second run; the first run crashed at N = 1e20 with an int64 overflow in the engine and printed identical lines for 1e16 and 1e18; the patch passes float counts)
```
N=1e16  T=34.6179  t_ve=-0.432415  that_ve=-0.432441  diff=+2.62e-05  t_ef=-0.407943  width=0.024472
      at midpoint t=-0.420179: edge-vertex=+0.012414  edge-full=+0.012414  edge-edge02=+0.689510  [2D-1D=+3.1e-13, lattice-real=+0.0e+00, trunc=0.0e+00]
N=1e18  T=39.1610  t_ve=-0.435624  that_ve=-0.435644  diff=+2.04e-05  t_ef=-0.410967  width=0.024657
      at midpoint t=-0.423295: edge-vertex=+0.012487  edge-full=+0.012486  edge-edge02=+0.689935  [2D-1D=+8.2e-13, lattice-real=+0.0e+00, trunc=0.0e+00]
N=1e20  T=43.7110  t_ve=-0.438254  that_ve=-0.438270  diff=+1.64e-05  t_ef=-0.413451  width=0.024803
      at midpoint t=-0.425852: edge-vertex=+0.012544  edge-full=+0.012544  edge-edge02=+0.690271  [2D-1D=+0.0e+00, lattice-real=+0.0e+00, trunc=nan]
```
Verdict: P6' survives. (i) |t_ve - that_ve| = 2.6e-5, 2.0e-5, 1.6e-5 (< 5e-4). (ii) widths 0.024472, 0.024657, 0.024803, in [0.0240, 0.0261] and increasing. (iii) at the window midpoints the edge beats vertex and full face by +0.0124 to +0.0125 and the other edges by +0.69 (log 2 = 0.693 in the limit). Post hoc: T*(0.026050 - width) = 0.0547, 0.0546, 0.0546, so the width is 0.026050 - 0.0546/T + o(1/T).

### P7 outcome (C5_P7_cT.py, verbatim output; the chunked torus code was first checked against the run-count engine at three random-generator cells: agreement 7e-15 or better)
```
(a) 4-cycle pair: k=2 lambda=1.000000000000 K_F=0.398942280401 alpha*=[0.5 0.5]
   T=  25 K= 184  R=-5.051217282659e-03  T*R=-0.126280432  quad-check=+3.6e-15  argmax=[0.5 0.5]
   T=  50 K= 232  R=-2.512648895248e-03  T*R=-0.125632445  quad-check=+0.0e+00  argmax=[0.5 0.5]
   T= 100 K= 304  R=-1.253143417557e-03  T*R=-0.125314342  quad-check=+0.0e+00  argmax=[0.5 0.5]
   T= 200 K= 400  R=-6.257835403574e-04  T*R=-0.125156708  quad-check=+0.0e+00  argmax=[0.5 0.5]
   T= 400 K= 544  R=-3.126955980974e-04  T*R=-0.125078239  quad-check=+0.0e+00  argmax=[0.5 0.5]
   Richardson-1: [-0.124984 -0.124996 -0.124999 -0.125   ]   Richardson-2: [-0.125 -0.125 -0.125]
(b) K_3 full, mu uniform: k=3 lambda=-0.000000000000 K_F=1.240490014699 alpha*=[0.333333 0.333333 0.333333]
   T=  25 K=  93  R=-1.008494362849e-02  T*R=-0.252123591  quad-check=+0.0e+00  argmax=[0.3333333 0.3333333 0.3333333]
   T=  50 K= 111  R=-5.021031108595e-03  T*R=-0.251051555  quad-check=+0.0e+00  argmax=[0.3333333 0.3333333 0.3333333]
   T= 100 K= 138  R=-2.505232844474e-03  T*R=-0.250523284  quad-check=+0.0e+00  argmax=[0.3333333 0.3333333 0.3333333]
   T= 200 K= 175  R=-1.251305134406e-03  T*R=-0.250261027  quad-check=+0.0e+00  argmax=[0.3333333 0.3333333 0.3333333]
   T= 400 K= 228  R=-6.253259017130e-04  T*R=-0.250130361  quad-check=+0.0e+00  argmax=[0.3333333 0.3333333 0.3333333]
   Richardson-1: [-0.24998  -0.249995 -0.249999 -0.25    ]   Richardson-2: [-0.25 -0.25 -0.25]
(c) 4-cycle 3-arc: k=3 lambda=0.585786437627 K_F=0.655928504743 alpha*=[0.25 0.5  0.25]
   T=  25 K=  93  R=-9.370317844841e-03  T*R=-0.234257946  quad-check=-3.6e-15  argmax=[0.2439313 0.5121375 0.2439313]
   T=  50 K= 111  R=-4.663269551582e-03  T*R=-0.233163478  quad-check=+0.0e+00  argmax=[0.247019  0.5059621 0.247019 ]
   T= 100 K= 138  R=-2.326795812422e-03  T*R=-0.232679581  quad-check=+0.0e+00  argmax=[0.2485226 0.5029548 0.2485226]
   T= 200 K= 175  R=-1.162259245149e-03  T*R=-0.232451849  quad-check=+0.0e+00  argmax=[0.2492645 0.5014709 0.2492645]
   T= 400 K= 228  R=-5.808533904883e-04  T*R=-0.232341356  quad-check=+0.0e+00  argmax=[0.2496331 0.5007338 0.2496331]
   Richardson-1: [-0.232069 -0.232196 -0.232224 -0.232231]   Richardson-2: [-0.232238 -0.232234 -0.232233]
(d) 4-cycle full: k=4 lambda=-0.000000000000 K_F=1.436696977001 alpha*=[0.25 0.25 0.25 0.25]
   T=  25 K=  75  R=-2.271645436224e-02  T*R=-0.567911359  quad-check=+0.0e+00  argmax=[0.25 0.25 0.25 0.25]
   T=  50 K=  89  R=-1.130361013794e-02  T*R=-0.565180507  quad-check=+0.0e+00  argmax=[0.25 0.25 0.25 0.25]
   T= 100 K= 110  R=-5.638341347892e-03  T*R=-0.563834135  quad-check=+0.0e+00  argmax=[0.25 0.25 0.25 0.25]
   T= 200 K= 138  R=-2.815827791645e-03  T*R=-0.563165558  quad-check=+0.0e+00  argmax=[0.25 0.25 0.25 0.25]
   Richardson-1: [-0.56245  -0.562488 -0.562497]   Richardson-2: [-0.5625 -0.5625]
```
Verdict: P7 survives. c_pair = -0.125000 (|diff| < 1e-6), c_K3 = -0.250000, c_arc = -0.232233 (in [-0.236, -0.228]), c_full(4-cycle) = -0.562500 (in [-0.58, -0.55]; numerically -9/16). Cross-checks: P3' T_N(Khat-K) = -0.2333 at N = 1e14 against c_arc - c_vertex = -0.2322; P2 T_N(Khat-K) = -0.4405 at N = 1e8 against c_full - c_pair = -0.4375. The continuum arc maximiser sits at alpha_1 = 1/4 - 0.147/T, matching the discrete mode drift seen in P3 (T(1/4 - a/N) = 0.150 at N = 1e14).

### P8 outcome (C5_P8_identities.py, verbatim output)
```
(a) Legendre identity det(Sigma) det(Hess I) = 1, random non-reversible faces
  k=2 alpha=[0.378 0.622]  detSigma*detHessI - 1 = -2.95e-10
  k=2 alpha=[0.466 0.534]  detSigma*detHessI - 1 = -1.39e-10
  k=2 alpha=[0.335 0.665]  detSigma*detHessI - 1 = -5.10e-10
  k=3 alpha=[0.544 0.219 0.237]  detSigma*detHessI - 1 = -5.62e-09
  k=3 alpha=[0.139 0.096 0.765]  detSigma*detHessI - 1 = +5.25e-07
  k=3 alpha=[0.349 0.54  0.111]  detSigma*detHessI - 1 = -5.79e-08
  k=4 alpha=[0.283 0.245 0.152 0.32 ]  detSigma*detHessI - 1 = +8.91e-09
  k=4 alpha=[0.365 0.291 0.204 0.14 ]  detSigma*detHessI - 1 = -2.16e-08
  k=4 alpha=[0.295 0.144 0.367 0.194]  detSigma*detHessI - 1 = -1.19e-08
  k=5 alpha=[0.197 0.147 0.198 0.207 0.252]  detSigma*detHessI - 1 = +1.66e-07
  k=5 alpha=[0.248 0.122 0.085 0.182 0.363]  detSigma*detHessI - 1 = -2.02e-07
  k=5 alpha=[0.224 0.166 0.206 0.14  0.264]  detSigma*detHessI - 1 = +6.95e-08
  worst |.-1| = 5.25e-07
(b) reversible faces: tree formula, sqrt tilts, Dupuis-Liu rate
  k=2  detSigma/tree-1=+0.00e+00  r err=2.2e-16  I err=2.2e-16
  k=2  detSigma/tree-1=+1.78e-15  r err=1.2e-15  I err=0.0e+00
  k=2  detSigma/tree-1=+2.22e-16  r err=0.0e+00  I err=0.0e+00
  k=3  detSigma/tree-1=+2.85e-10  r err=1.5e-09  I err=3.3e-16
  k=3  detSigma/tree-1=-6.20e-08  r err=2.7e-08  I err=0.0e+00
  k=3  detSigma/tree-1=-5.47e-14  r err=1.3e-13  I err=4.4e-16
  k=4  detSigma/tree-1=-2.47e-13  r err=1.7e-13  I err=2.2e-16
  k=4  detSigma/tree-1=+4.52e-11  r err=5.1e-11  I err=1.1e-16
  k=4  detSigma/tree-1=+3.20e-11  r err=6.8e-11  I err=4.4e-16
  k=5  detSigma/tree-1=+1.29e-09  r err=6.6e-10  I err=4.4e-16
  k=5  detSigma/tree-1=-5.05e-10  r err=6.8e-10  I err=0.0e+00
  k=5  detSigma/tree-1=-8.33e-10  r err=2.9e-10  I err=2.2e-16
  k=6  detSigma/tree-1=+1.06e-09  r err=4.7e-10  I err=4.4e-16
  k=6  detSigma/tree-1=-1.18e-08  r err=6.5e-09  I err=4.4e-16
  k=6  detSigma/tree-1=-2.55e-10  r err=2.7e-10  I err=2.2e-16
  worst = 6.20e-08
(c) non-reversible faces: det Sigma vs the reversiblised tree bound
  k=3  detSigma/bound = 0.977261827
  k=3  detSigma/bound = 0.952461775
  k=3  detSigma/bound = 0.995854730
  k=3  detSigma/bound = 0.999974085
  k=4  detSigma/bound = 0.989062137
  k=4  detSigma/bound = 0.976450591
  k=4  detSigma/bound = 0.984395369
  k=4  detSigma/bound = 0.992134555
  k=5  detSigma/bound = 0.962585980
  k=5  detSigma/bound = 0.891069474
  k=5  detSigma/bound = 0.869098914
  k=5  detSigma/bound = 0.887876089
  max ratio = 0.999974085, min ratio = 0.869098914
```
Verdict: (a) survives (worst 5.3e-7 < 1e-5). (c) survives (all 12 ratios below 1, the closest 0.999974, none within 1e-6 of equality). (b) is KILLED by the letter of its criterion: one k = 3 instance has det Sigma / tree - 1 = -6.2e-8 > 1e-9 (and three others exceed 1e-9). Diagnosis (after the run): in every row the mismatch tracks the error of the numerically optimised tilt ("r err", e.g. 2.7e-8 in the worst row), i.e. BFGS precision, not the identity; the 1e-9 tolerance was tighter than the optimiser delivers. Corrected test P8(b') registered below.

## 2026-09-25 P8(b') (registered after P8(b) was killed)
Same random reversible instances regenerated with a new seed (2027), k = 2..7, 4 per k. Build the Doob transform from the exact tilt r = sqrt(alpha/nu) (no optimiser) and check: (1) stationarity: the gradient of w -> sum_i alpha_i sum_j a_ij e^{w_j - w_i} at w = log r vanishes; (2) det Sigma (from the fundamental matrix) equals 2^{k-1} (prod alpha)^2 / tau(c). Kill: |grad| > 1e-12 or relative mismatch > 1e-10 in any instance.

### P8(b') outcome (C5_P8b_exact.py, verbatim output)
```
  k=2  |grad|=2.8e-17  pi check=2.8e-17  detSigma/tree-1=-2.22e-16
  k=2  |grad|=0.0e+00  pi check=0.0e+00  detSigma/tree-1=-1.11e-16
  k=2  |grad|=2.8e-17  pi check=2.8e-17  detSigma/tree-1=+4.44e-16
  k=2  |grad|=0.0e+00  pi check=0.0e+00  detSigma/tree-1=+1.33e-15
  k=3  |grad|=5.6e-17  pi check=5.6e-17  detSigma/tree-1=+8.88e-16
  k=3  |grad|=5.6e-17  pi check=5.6e-17  detSigma/tree-1=-7.77e-16
  k=3  |grad|=2.2e-16  pi check=2.2e-16  detSigma/tree-1=-3.33e-16
  k=3  |grad|=1.1e-16  pi check=2.8e-17  detSigma/tree-1=+0.00e+00
  k=4  |grad|=1.1e-16  pi check=1.1e-16  detSigma/tree-1=+2.22e-15
  k=4  |grad|=1.7e-16  pi check=1.7e-16  detSigma/tree-1=-3.33e-16
  k=4  |grad|=5.6e-17  pi check=5.6e-17  detSigma/tree-1=+4.44e-16
  k=4  |grad|=3.3e-16  pi check=2.2e-16  detSigma/tree-1=-1.57e-14
  k=5  |grad|=5.6e-17  pi check=5.6e-17  detSigma/tree-1=+4.29e-14
  k=5  |grad|=1.1e-16  pi check=1.1e-16  detSigma/tree-1=-2.11e-15
  k=5  |grad|=5.6e-17  pi check=5.6e-17  detSigma/tree-1=+2.22e-15
  k=5  |grad|=1.1e-16  pi check=1.7e-16  detSigma/tree-1=+6.66e-16
  k=6  |grad|=5.6e-17  pi check=2.8e-17  detSigma/tree-1=-1.18e-14
  k=6  |grad|=5.6e-17  pi check=5.6e-17  detSigma/tree-1=+2.00e-15
  k=6  |grad|=1.1e-16  pi check=1.1e-16  detSigma/tree-1=+9.33e-15
  k=6  |grad|=1.1e-16  pi check=8.3e-17  detSigma/tree-1=+3.77e-15
  k=7  |grad|=1.7e-16  pi check=1.4e-16  detSigma/tree-1=-1.11e-15
  k=7  |grad|=5.6e-17  pi check=6.2e-17  detSigma/tree-1=-1.84e-14
  k=7  |grad|=2.2e-16  pi check=1.7e-16  detSigma/tree-1=-4.44e-15
  k=7  |grad|=1.1e-16  pi check=8.3e-17  detSigma/tree-1=+0.00e+00
worst |grad| = 3.33e-16, worst rel mismatch = 4.29e-14
```
Verdict: P8(b') survives (worst |grad| 3.3e-16, worst relative mismatch 4.3e-14, k = 2..7).

### P9 outcome (C5_P9_P10.py P9, verbatim output)
```
P9: 4-cycle 3-arc vs pair, predicted K = 0.497235050554
  N=1e4  T_N=17.565217543  Khat=0.501628704  Khat-K=+4.3937e-03  T(Khat-K)=+0.07718  arc argmax a/N=0.241262  2D-1D=+5.0e-14  lattice-real=-1.3e-07  trunc arc/pair=0e+00/0e+00  pred T=17.29121
  N=1e6  T_N=28.133696910  Khat=0.493667720  Khat-K=-3.5673e-03  T(Khat-K)=-0.10036  arc argmax a/N=0.244629  2D-1D=+8.5e-14  lattice-real=-9.2e-12  trunc arc/pair=0e+00/0e+00  pred T=27.91964
  N=1e8  T_N=38.859739894  Khat=0.494470074  Khat-K=-2.7650e-03  T(Khat-K)=-0.10745  arc argmax a/N=0.246145  2D-1D=+1.7e-13  lattice-real=+1.1e-13  trunc arc/pair=0e+00/0e+00  pred T=38.69024
  N=1e10  T_N=49.679644894  Khat=0.495070596  Khat-K=-2.1645e-03  T(Khat-K)=-0.10753  arc argmax a/N=0.246999  2D-1D=+5.7e-14  lattice-real=-5.7e-14  trunc arc/pair=0e+00/0e+00  pred T=49.53875
  N=1e12  T_N=60.557562157  Khat=0.495460390  Khat-K=-1.7747e-03  T(Khat-K)=-0.10747  arc argmax a/N=0.247546  2D-1D=+2.6e-13  lattice-real=-5.7e-14  trunc arc/pair=0e+00/0e+00  pred T=60.43653
```
Verdict: P9 survives. |Khat - K| = 1.77e-3 < 0.01 at N = 1e12; T_N(Khat - K) = -0.10747 in [-0.13, -0.085]. It agrees with c_arc - c_pair = -0.232233 + 0.125 = -0.107233 from P7 (continuum, independent) to 2.4e-4.

### P10 outcome (C5_P9_P10.py P10, verbatim output)
```
P10: random seed-7 generator, F={0,1,2} vs G={0,1}: delta=0.8096595675 K=0.6842375812 b=-0.7898082846  alpha*_F=[0.316032 0.387635 0.296333] alpha*_G=[0.243076 0.756924]
  N=1e4  T_N=9.179277246  Khat=0.669776491  Khat-K=-1.4461e-02  T(Khat-K)=-0.13274  F argmax=[0.31603  0.394746]  T(argmax-alpha*)=[-0.      0.0653]  lattice-real=-6.0e-08  trunc=0e+00  pred T=9.02894
  N=1e6  T_N=14.582582161  Khat=0.668669485  Khat-K=-1.5568e-02  T(Khat-K)=-0.22702  F argmax=[0.316057 0.391889]  T(argmax-alpha*)=[0.0004 0.062 ]  lattice-real=-1.5e-11  trunc=0e+00  pred T=14.46633
  N=1e8  T_N=20.068072607  Khat=0.672808694  Khat-K=-1.1429e-02  T(Khat-K)=-0.22936  F argmax=[0.316059 0.390651]  T(argmax-alpha*)=[0.0005 0.0605]  lattice-real=-8.5e-14  trunc=0e+00  pred T=19.97646
  N=1e10  T_N=25.602363289  Khat=0.675310210  Khat-K=-8.9274e-03  T(Khat-K)=-0.22856  F argmax=[0.316057 0.389966]  T(argmax-alpha*)=[0.0006 0.0597]  lattice-real=-1.1e-13  trunc=0e+00  pred T=25.52645
  N=1e12  T_N=31.166708123  Khat=0.676922457  Khat-K=-7.3151e-03  T(Khat-K)=-0.22799  F argmax=[0.316054 0.389533]  T(argmax-alpha*)=[0.0007 0.0592]  lattice-real=-9.9e-14  trunc=0e+00  pred T=31.10164
```
Verdict: P10 survives. |Khat - K| = 7.3e-3 < 0.03 at N = 1e12; |T_N(Khat-K)| = 0.228 < 1; it changes by 5.7e-4 between N = 1e10 and 1e12 (< 0.05). The non-symmetric maximiser drifts as alpha* + (0.0007, 0.059)/T, the O(1/T) shift the theory predicts.

### Erratum note (2026-09-25, appended; nothing above is changed)
In the P4 registration the local law is written "(T/2pi)^{(k-1)/2} C(alpha) e^{-T I(alpha)}". The code (C5_theory.tilt, C5_P4_local.py) and the header use C(alpha) = (mu.r)(l.1)(2pi)^{-(k-1)/2} det(Sigma)^{-1/2} and compare against T^{(k-1)/2} C(alpha) e^{-T I(alpha)}. These are the same prediction; the P4 line double-writes the (2pi) factor in its notation only. The tested quantity is the one in the code, and it is the one proved as Theorem 3 in C5.md.

## 2026-09-25 Erratum to the P6 registration (appended; the registration above is unchanged)
The P6 registration gives the upper end of the limiting edge window as -0.441306. The correct value of (1/2)log(2/pi) - log(3^{5/2}/(4 pi)) is -0.4412978 (hand check: -0.2257914 - 0.2155065), so the limiting width is 0.0260580, not 0.02605. Found by an independent verifier (V1). P6's verdict (killed) does not change: its failure came from the log L/L drift at finite N, not from this digit. P6' used the width interval [0.024, 0.0261], which contains both values, so its verdict does not change either.

## 2026-09-25 R1 (reducible faces; registered after the verifier's V5 report, before any C5 code touches these cells)
Model: d = 3, rates a_12 = b, a_23 = a_31 = 1 (all other rates 0), mu = delta_1. Admissible faces: {1}; {1,2} (reducible, SCCs {1},{2}); {1,2,3} (irreducible, lambda = 0). Hand results written in C5.md before running (Prop. 19): M_1 = (1-bh)^{N-1}; M_12 = bh(1-h)^{N-2} exactly (attained at n = (1,N-1,0)); K_123 = (1+2b)^2/(2 sqrt3 pi b), from alpha* = (1,b,b)/(1+2b) and det Hess I = (1+2b)^4/(3b^2).
(a) Closed form. For b in {3, 4, 5, 10}, K_123 from C5_theory.quasi_ergodic equals (1+2b)^2/(2 sqrt3 pi b) (b = 4: 27 sqrt3/(8 pi) = 1.8607350). Kill: relative mismatch > 1e-10.
(b) First crossing, b = 3 (new cell), N = 1e6, 1e9, 1e12: the root of log M_12 = log M_1 satisfies |2T + log T - (L - log 3)| <= 5 T^2/N, and T_N - (1/2)[L - log L + log(2/3)] is positive, decreasing in N, and in [0.04, 0.10] at N = 1e12 (so the log log N coefficient is 1, not 1/2). Kill: any of these fails.
(c) Second crossing, b = 3 (new cell): with M_123 the exact discrete maximum over bins with all three counts >= 1 (run-count engine plus lattice search), the root of log M_12 = log M_123 has |T_N - L - 0.692587| < 0.03 at N = 1e6 and 1e8 (limit log b - log K_123 = log(18 sqrt3 pi/49)), and T_N (T_N - L - 0.692587) changes by less than 25% between the two N (log log coefficient 0). Kill: either fails.
(d) Brute-force DP of the full composition law, b = 3, N = 300 (new cell): total mass 1 to 1e-10; global mode (300,0,0) at T = 1.5; (1,299,0) at T = 3.5; a bin with all three counts >= 1 at T = 10. Kill: any mismatch.

## 2026-09-25 R2 (exact third-order coefficients; registered before the script is written)
c_F := lim_T T[max_alpha f_T(alpha)/(T^{(k-1)/2} K_F e^{-T lambda_F}) - 1] = c_1(alpha*)/a_0 + (1/2) gamma^T Sigma gamma, where c_1/a_0 is the 1/T Wick coefficient of Lemma 3A (C5.md) for the torus integral of Theorem 3 and gamma = grad log C_F at alpha* in the coordinates alpha_2..alpha_k. My own sympy implementation (not importing any verifier code).
(a) Exact values, uniform mu on [d]: 4-cycle pair -1/8; K_3 full face (d = 3) -1/4; K_4 full face (d = 4) -3/8; 4-cycle full face -9/16; 4-cycle 3-arc 5 sqrt2/4 - 2 = -0.2322330470 (this last value was reported by a verification pass; the others are Paper A, Paper B and P7). Kill: any exact result that differs from the stated closed form (difference not simplifying to 0, or numerically > 1e-25).
(b) Non-symmetric cell: the seed-7 random generator of P10, mu uniform, F = {0,1,2}, G = {0,1}. The Wick value (derivatives exact in sympy, evaluated with 30 digits; gamma by high-precision central differences of log C_F) gives c_F - c_G in [-0.232, -0.221]. Point guess -0.2254, from a/T extrapolation of P10's T(Khat - K) at N = 1e10, 1e12. Also (c) the continuum c_F of the same F computed from the run-count engine, Richardson in T over {25, 50, 100, 200} as in P7, agrees with the Wick value to 2e-3. Kill: (b) outside the interval, or (c) mismatch > 2e-3.

### R1 outcome (C5_R1_reducible.py, parts a, b, d; verbatim output)
```
(a) K_123 numeric (quasi_ergodic) vs (1+2b)^2/(2 sqrt3 pi b)
  b= 3.0: lambda=-9.18e-17 alpha*=[0.142857 0.428571 0.428571] K=1.500839770870 closed=1.500839770870 rel=+2.66e-15
  b= 4.0: lambda=+1.03e-16 alpha*=[0.111111 0.444444 0.444444] K=1.860735022049 closed=1.860735022049 rel=-6.66e-16
  b= 5.0: lambda=+5.63e-17 alpha*=[0.090909 0.454545 0.454545] K=2.223693211535 closed=2.223693211535 rel=-1.05e-14
  b=10.0: lambda=+3.67e-17 alpha*=[0.047619 0.47619  0.47619 ] K=4.052267381350 closed=4.052267381350 rel=+2.64e-14
  b=4 closed 27 sqrt3/(8 pi) = 1.8607350220
(b) first crossing {1} vs {1,2}, b = 3
  N=1e6: T1=5.505516014619 residual 2T+logT-(L-log3)=-1.157e-04 (bound 5T^2/N=1.52e-04)  T1-(1/2)[L-logL+log(2/3)]=+0.113389
  N=1e9: T1=8.729001152236 residual 2T+logT-(L-log3)=-2.961e-07 (bound 5T^2/N=3.81e-07)  T1-(1/2)[L-logL+log(2/3)]=+0.085729
  N=1e12: T1=12.022801910364 residual 2T+logT-(L-log3)=-5.662e-10 (bound 5T^2/N=7.23e-10)  T1-(1/2)[L-logL+log(2/3)]=+0.069493
(d) brute-force DP, b = 3, N = 300
  T= 1.50: total mass=1.0000000000000  global mode (n1,n2,n3)=(300,0,0)  P=1.090016e-02
  T= 3.50: total mass=1.0000000000000  global mode (n1,n2,n3)=(1,299,0)  P=1.059971e-03
  T=10.00: total mass=1.0000000000000  global mode (n1,n2,n3)=(44,135,121)  P=1.757254e-04
```
### R1 outcome (C5_R1_reducible.py, part c; verbatim output)
```
(c) second crossing {1,2} vs {1,2,3}, b = 3
  K_123=1.500839770870  limit log b - log K = 0.692587
  N=1e6: T2=14.513052702  T2-L=0.697542  dev=+0.004955  T2*dev=+0.07191  argmax=[0.144232 0.443701]  trunc=0e+00
  N=1e8: T2=19.117112263  T2-L=0.696432  dev=+0.003844  T2*dev=+0.07349  argmax=[0.143906 0.439853]  trunc=0e+00
  relative change of T*dev between the two N: 0.022

```
Verdict: R1 survives. (a) closed form K_123 = (1+2b)^2/(2 sqrt3 pi b) matches to <= 2.7e-14 for b = 3, 4, 5, 10. (b) residuals -1.16e-4, -2.96e-7, -5.66e-10 are inside 5T^2/N (they equal (1-b^2)T^2/(2N) + (b-2)h to leading order, i.e. -4T^2/N + h here); T_1 - (1/2)[L - log L + log(2/3)] = 0.1134, 0.0857, 0.0695: positive, decreasing, in [0.04, 0.10] at 1e12, so the loglog coefficient of this crossing is 1. (c) T_2 - L - 0.692587 = +0.00496, +0.00384 (< 0.03); T_2 * dev = 0.0719, 0.0735 (change 2.2% < 25%), so the loglog coefficient is 0. (d) DP at N = 300 has total mass 1 and modes (300,0,0), (1,299,0), (44,135,121) at T = 1.5, 3.5, 10, as registered. Remark after the run (not registered): T_2 * dev -> -c_123 in the notation of Prop. 16, so this suggests c_123 ~ -0.07 for the b = 3 directed cycle; not computed.

### R2 outcome, part (a) (C5_R2_exact_c.py a; verbatim output)
```
(a) exact c_F, uniform start on [d]
  4-cycle pair: c(alpha*) = -1/8   (gamma = 0 by the swap symmetry)   predicted -1/8: diff = 0
  K_3 full: c(alpha*) = -1/4   predicted -1/4: diff = 0
  K_4 full: c(alpha*) = -3/8   predicted -3/8: diff = 0
  4-cycle full: c(alpha*) = -9/16, gamma term = 0, c_F = -9/16   predicted -9/16: diff = 0   [C(alpha*) = 8/pi**(3/2), 8/pi^(3/2) check: 0]
  4-cycle 3-arc: c(alpha*) = 2 - 7*sqrt(2)/4 (end state distinguished) = 2 - 7*sqrt(2)/4 (middle distinguished); diff = 0
     gamma term = -4 + 3*sqrt(2) = 0.24264068711928514641;  c_F = -2 + 5*sqrt(2)/4 = -0.23223304703363118900
     predicted 5 sqrt2/4 - 2: diff = 0   [C(alpha*) = (4 + 3*sqrt(2))/(4*pi)]
     implied residuals: c_arc - c_pair = -0.107233047033631 (P9 obs -0.10747); c_arc - c_vertex = -0.232233047033631 (P3' obs -0.2333); c_full - c_pair = -7/16 (P2 obs -0.4405)
```
Verdict (a): survives. Every exact value equals its registered closed form (sympy difference 0): pair -1/8, K_3 -1/4, K_4 -3/8, 4-cycle full -9/16 (gamma term 0), 3-arc 5 sqrt2/4 - 2 = c(alpha*) + gamma term = (2 - 7 sqrt2/4) + (3 sqrt2 - 4). Internal check: c(alpha*) for the 3-arc is the same with the end state or the middle state distinguished. The K_3, K_4 and pair values reproduce the proved Paper B / Bessel values, which checks the implementation.

### R2 outcome, part (b) (C5_R2_exact_c.py b; verbatim output)
```
(b) P10 faces, seed-7 generator, mu uniform
   Q = [[-4.016592026169649    1.8149848417452359   1.5962342424413483
   0.6053729419830653 ]
 [ 0.7402993128402058  -2.6279880141472196   0.20947754821803452
   1.6782111530889794 ]
 [ 1.6347249717536831   1.0422829151186974  -3.3781739886537725
   0.7011661017813919 ]
 [ 0.6587652577774243   1.001137350588764    1.108186866124316
  -2.7680894744905045 ]]
   F={0,1,2}: lambda=1.16145048434393 alpha*=['0.31603234', '0.38763495', '0.29633271'] K=1.04236132409981  c(alpha*)=-0.233304882623 (imag +0.0e+00)  gamma=['0.08426358547', '-0.3218434132']  gamma term=0.0116864890451  c_F=-0.221618393578  [radii residual max|rho(tilt)-rho|=1.61e-40]
   G={0,1}: lambda=1.97111005186754 alpha*=['0.24307567', '0.75692433'] K=0.525844920416348  c(alpha*)=-0.132734907459 (imag +0.0e+00)  gamma=['1.415935887']  gamma term=0.136501663945  c_F=0.00376675648575  [radii residual max|rho(tilt)-rho|=9.18e-41]
   c_F - c_G = -0.225385150063   (registered interval [-0.232, -0.221]; P10 T(Khat-K) = -0.22856, -0.22799 at 1e10, 1e12)
   predicted maximiser drift T(argmax - alpha*) in (alpha_1, alpha_2) = ['0.0568201', '-0.0577458']  (P10 observed (0.0007, 0.0592) at 1e12)
```
Verdict (b): survives. c_F - c_G = -0.225385150 lies in [-0.232, -0.221] and is within 5e-5 of the registered point guess -0.2254 (a/T extrapolation of P10's data). Printed but not registered: the predicted drift Sigma gamma/T of the F-maximiser is (0.0568, -0.0577) in (alpha_1, alpha_2), i.e. (0.0009, 0.0568) in P10's coordinates (alpha_0, alpha_1), against P10's discrete (0.0007, 0.0592) at N = 1e12 (T = 31).

### R2 outcome, part (c) (C5_R2_exact_c.py c; verbatim output)
```
(c) continuum c_F, F={0,1,2}: lambda=1.161450484344 K=1.042361324100 alpha*=[0.316032 0.387635 0.296333]
   T=  25 Kq=93  T*R=-0.223097391  quad-check=-7.1e-15  T(argmax-alpha*)=[ 0.00061  0.05977 -0.06038]
   T=  50 Kq=111  T*R=-0.222352484  quad-check=+0.0e+00  T(argmax-alpha*)=[ 0.00077  0.05826 -0.05904]
   T= 100 Kq=138  T*R=-0.221984129  quad-check=+0.0e+00  T(argmax-alpha*)=[ 0.00085  0.05753 -0.05838]
   T= 200 Kq=175  T*R=-0.221800939  quad-check=+0.0e+00  T(argmax-alpha*)=[ 0.00089  0.05717 -0.05806]
   Richardson-1: [-0.221608 -0.221616 -0.221618]   Richardson-2: [-0.221619 -0.221618]
```
Verdict (c): survives. The continuum Richardson-2 values -0.221619, -0.221618 agree with the Wick value c_F = -0.2216184 from (b) to about 1e-6 (tolerance 2e-3). Printed but not registered: the continuum maximiser drift T(argmax - alpha*) tends to (0.00089, 0.05717, -0.05806) at T = 200, consistent with Sigma gamma/T = (alpha_1, alpha_2) drift (0.0568, -0.0577) from (b) (alpha_0 component 0.0009). R2 as a whole survives.
