# Problem 131 Paper D, topic D2 ledger (elephant profile and shape at the crossing): predictions with kill conditions, written before the computations that test them; outcomes appended verbatim below each.

Conventions. ERW with symmetric start, mutation (flip) probability eps = x/n, A_n = number of +1 steps, m = n - A_n. h(m) = P(M_n = m | X_1 = +), so P(A_n = n-m) = (h(m) + h(n-m))/2. CP_n = compound Poisson law with jump d in [1, n-1] at rate x/(d(d+1)) (code/D2_lib.py, cp_law). R(m) = P(A_n = n-m)/(x/m^2), the ratio printed by erw.py. Reproduction of the already reported cell n = 1600 (code/D2_reproduce.py, D2_check1600.py) gave x_1600 = 10.240565, mode m = 21, interior minimum at the center, R(80) = 1.0033, R(160) = 0.806, R(400) = 0.671, R(800) = 1.086, h/CP_n between 0.931 and 1.023.

## 2026-09-25 D2-P1 (n = 3200, exact crossing x_3200 ~ 11.547): mode
Prediction: the upper-half mode of P(A_n = a) is at m* = n - a* = 25 (the CP_n mode at x = 11.547; Landau asymptotic x log x - 0.2228 x = 25.7; the program's "about 2x" rule would give 23).
Kill: m* not in {24, 25, 26}.

## 2026-09-25 D2-P2 (n = 3200, exact crossing): profile ratios R(m) = P(A_n = n-m)/(x/m^2)
Prediction (CP_n plus mirror term x/((n-m)(n-m+1)), with the finite-n factor h/CP_n extrapolated from n = 1600 by the factor 0.62 = (x log n / n at 3200)/(same at 1600)):
R(50) = 1.04, R(100) = 1.03, R(200) = 0.81, R(400) = 0.66, R(800) = 0.63, R(1600) = 1.054.
Kill: |observed/predicted - 1| > 0.03 at any of these six m.

## 2026-09-25 D2-P3 (n = 3200, exact crossing): shape
Prediction: P(A_n = a) is strictly increasing on [n/2, n - m*] and strictly decreasing on [n - m*, n] (W shape: the center is the unique interior minimum, exactly two interior maxima at m* and n - m*, endpoint atom below its neighbour). P(A_n = n-1)/P(A_n = n) lies in [5.5, 6.0] (theory: about x/2 = 5.77).
Kill: any other sign change of the first difference on the upper half, or the ratio outside [5.5, 6.0].

## 2026-09-25 D2-P4 (n = 3200, exact crossing): distance to CP_n
Prediction: over 1 <= m <= n/2, min h(m)/CP_n(m) lies in [0.95, 0.97] (attained near m = n/2) and max h(m)/CP_n(m) lies in [1.005, 1.03] (attained in the bulk, m about 10 to 25).
Kill: either extreme outside its interval.

## 2026-09-25 D2-P5 (n = 10^6, x = 22.4407 = root of x + log x = 2 log n - log 8): the tail constant is 1/2, not 1
Prediction: h(m) m(m+1)/x at m = 10^4 equals the CP_n value 1.0381 to within 1%, so R(10^4) = P(A_n = n - 10^4)/(x/10^8) is 0.519 +- 0.010. Also h(m) m(m+1)/x at m = 2000 and 5000 equal CP_n (1.1648, 1.0713) within 1%.
Kill: R(10^4) outside [0.509, 0.529], or any of the three h m(m+1)/x values off CP_n by more than 1%. (The program's "P(S_n = n-m) ~ x/m^2" corresponds to R -> 1.)

## 2026-09-25 D2-P6 (n = 10^6 and 10^5): mode location is x log x - 0.2228 x + O(1), not 2x
Prediction: exact upper-half mode m* at n = 10^6: x = 22.4407 -> 64 +- 1; x = 40 -> 137 +- 2; x = 80 -> 331 +- 2. At n = 10^5, x = 18.0531 -> 47 +- 1. (The 2x rule gives 45, 80, 160, 36.)
Kill: any m* outside its stated window.

## 2026-09-25 D2-P7 (n = 10^6, x = 22.4407): bulk agreement with CP_n
Prediction: max over 1 <= m <= 10^4 of |h(m)/CP_n(m) - 1| is at most 0.005.
Kill: larger than 0.005.

### Outcome of D2-P1..P4 (code/D2_run3200.py, run 2026-09-25 after the predictions above), verbatim output:
```
n=3200 crossing x=11.546834; sum P=1.000000000000003
P1 mode m* = 25  P at m*-1,m*,m*+1: 0.008689068055999487 0.008692450549317755 0.008661050188193598
P2 R(m) = P(A=n-m)/(x/m^2):
   m=   50 R=1.0306 pred=1.04 obs/pred-1=-0.0090
   m=  100 R=1.0160 pred=1.03 obs/pred-1=-0.0136
   m=  200 R=0.7998 pred=0.81 obs/pred-1=-0.0126
   m=  400 R=0.6605 pred=0.66 obs/pred-1=+0.0008
   m=  800 R=0.6268 pred=0.63 obs/pred-1=-0.0051
   m= 1600 R=1.0532 pred=1.054 obs/pred-1=-0.0007
P3 sign changes of first difference on upper half at a = [3175] ; zero diffs: 0
   interior argmin a = 1600 ; P(n-1)/P(n) = 5.804837539828846
P4 min h/CP=0.9558 at m=1600; max h/CP=1.0140 at m=20
```
Verdicts: D2-P1 survives (m* = 25). D2-P2 survives (largest deviation 1.4%, at m = 100). D2-P3 survives (one sign change, at a = 3175, i.e. m = 25; interior argmin at the center; ratio 5.80). D2-P4 survives (min 0.9558 at m = 1600, max 1.0140 at m = 20).

### Outcome of D2-P5, P6, P7 (code/D2_runbig.py, run 2026-09-25 after the predictions above), verbatim output:
```
n=1000000 x=40.0: mode m* = 137; CP_n mode = 137
n=1000000 x=80.0: mode m* = 331; CP_n mode = 331
time 7.514228582382202
n=100000 x=18.0531: mode m* = 47; CP mode 47; max|h/CP-1| (m<=5000) = 2.60e-03
   m=500: h m(m+1)/x = 1.47315, CP: 1.47573
   m=1000: h m(m+1)/x = 1.24411, CP: 1.24665
   m=2000: h m(m+1)/x = 1.12766, CP: 1.13024
   m=5000: h m(m+1)/x = 1.05426, CP: 1.05701
time 9.089691638946533
time 28.93167209625244
n=1000000 x=22.4407: mode m* = 64; CP mode 64
P7 max|h/CP-1| over 1..10000 = 3.532e-04 at m=10000
P5 m=2000: h m(m+1)/x = 1.16444  CP = 1.16477  mirror h(n-m) m(m+1)/x = 3.970e-06
P5 m=5000: h m(m+1)/x = 1.07092  CP = 1.07127  mirror h(n-m) m(m+1)/x = 2.514e-05
P5 m=10000: h m(m+1)/x = 1.03777  CP = 1.03814  mirror h(n-m) m(m+1)/x = 1.018e-04
P5 R(10^4) = P(A=n-m)/(x/m^2) = 0.51889
```
Verdicts: D2-P5 survives (R(10^4) = 0.5189 in [0.509, 0.529]; the three h m(m+1)/x values agree with CP_n to 0.04%). The program's "P(S_n = n-m) ~ x/m^2" (R -> 1) is refuted as an asymptotic statement: R -> 1/2. D2-P6 survives (64, 137, 331, 47 exactly equal to the CP_n modes; the 2x rule gives 45, 80, 160, 36). D2-P7 survives (max |h/CP_n - 1| = 3.5e-4 <= 0.005).

## 2026-09-25 D2-P8 (every n from 10 to 400, each at its exact crossing x_n): shape
Prediction: for every such n, (i) P(A_n = n-1) > P(A_n = n) (endpoint below its neighbour; the theorem gives this whenever x_n >= 2(1 - x_n/n)); (ii) the first difference of P(A_n = a) on the upper half a in [ceil(n/2), n] changes sign exactly once (from + to -), so the law is W-shaped with the center (n even) or the two central values (n odd) as the only interior local minima; (iii) for even n the interior argmin is a = n/2. Also: the smallest n >= 2 with x_n >= 2(1 - x_n/n) is at most 10.
Kill: any n in [10, 400] violating (i), (ii) or (iii), or the last statement false.

## 2026-09-25 D2-P9 (convexity of h, i.e. of the law given the first step)
Prediction: h(m) = P(M_n = m | X_1 = +) has strictly positive second differences for all m in [2 m*, n - 2 m*] (m* = mode of h), at the crossing, for n = 1600, 3200 and for every n in [100, 400].
Kill: any nonpositive second difference in that range for any of these n.

### Outcome of D2-P8 and D2-P9 (code/D2_shape_scan.py, run 2026-09-25 after the predictions above), verbatim output:
```
smallest n with x_n >= 2(1-eps_n): 8
  n=   2 x_n=0.6666666666666952
  n=   3 x_n=0.8786796564403575
  n=   4 x_n=1.0717967697244914
  n=   5 x_n=1.2262680656486664
  n=   6 x_n=1.3784220517210215
  n=   7 x_n=1.5028488026934326
  n=   8 x_n=1.6300083544769288
  n=   9 x_n=1.7355378244836324
  n=  10 x_n=1.8455132405497863
  n=  11 x_n=1.9378586305048549
  n=  12 x_n=2.035148688853677
  n=  20 x_n=2.632592188987243
  n=  50 x_n=3.9404868664848887
  n= 100 x_n=5.095896673808848
  n= 200 x_n=6.34059016815592
  n= 400 x_n=7.629216896204109
D2-P8 violations (n, x, dip, sign changes, argmin_ok): []  count 0
D2-P9 violations (n, x, m*, first bad m): [(100, 5.095896673808848, 7, 82), (101, 5.112957014352746, 7, 82), (102, 5.130463534992903, 7, 83), (103, 5.1472305947899, 7, 84), (104, 5.164428320934837, 7, 85), (105, 5.180911972493414, 7, 86), (106, 5.197811541150175, 7, 86), (107, 5.21402116351373, 7, 87), (108, 5.230632670022388, 7, 88), (109, 5.246577181453298, 7, 89), (110, 5.262910215844632, 7, 90), (111, 5.278598103816213, 7, 90), (112, 5.29466178415106, 7, 91), (113, 5.3101011329119405, 7, 92), (114, 5.325904135899657, 7, 93), (115, 5.341102651845209, 7, 94), (116, 5.356653241005016, 7, 94), (117, 5.3716182760639315, 7, 95), (118, 5.386924327663216, 7, 96), (119, 5.401662900884712, 7, 97)]  count 301
n=1600: m*=21, min second difference on [43,1557] = -1.652e-09, all positive: False
   m with nonpositive second difference (m=2..n-2): first few [ 9 10 11 12 13 14 15 16], last few [1571 1572 1573 1574 1575 1576 1577 1578]
n=3200: m*=25, min second difference on [51,3149] = -3.436e-10, all positive: False
   m with nonpositive second difference (m=2..n-2): first few [11 12 13 14 15 16 17 18], last few [3167 3168 3169 3170 3171 3172 3173 3174]
```
Verdicts: D2-P8 survives (no violation for 10 <= n <= 400; the sufficient condition x_n >= 2(1 - eps_n) first holds at n = 8). D2-P9 is REFUTED: h is not convex on [2m*, n - 2m*]; for every n in [100, 400] it fails (first failure near m = 0.82 n), and at n = 1600, 3200 as well.
Diagnostic after the refutation (code/D2_convexity_probe.py): the second difference of h changes sign at m = 9, 33, 1399, 1579 (n = 1600) and 11, 39, 2867, 3175 (n = 3200), so h has a concave stretch n - m in [21, 201] (resp. [25, 333]) before its far-end drop; h(m) m(m+1)/x is 0.959 at n - m = 160 (n = 1600), i.e. the far end approaches x/n^2 slowly (deficit roughly x/(n-m)). The full law P(A_n = a) = (h(n-a) + h(a))/2 has second-difference sign changes only at a = 9, 33, 1568, 1592 (n = 1600) and 11, 39, 3162, 3190 (n = 3200): it is convex on [33, 1567] and [39, 3161]. This full-law convexity is a POST HOC observation; it is pre-registered as D2-P10 below before being tested on new cells.

## 2026-09-25 D2-P10 (post hoc observation turned into a prediction): convexity of the full law between the modes
Prediction: at the exact crossing, the second difference of a -> P(A_n = a) is strictly positive for all a in [a_1, n - a_1], where a_1 <= 2 m* (m* = upper-half mode distance, as before), for every n in [100, 400] and for n = 6400. At n = 6400 additionally: m* = CP_n mode at the crossing (computed from x_6400 after the crossing is found) and the sign changes of the second difference occur only inside the two bulks (a < 2m* or a > n - 2m*).
Kill: any nonpositive second difference in [2m*, n - 2m*] for any of these n.

### Outcome of D2-P10 (code/D2_fullconvex.py, run 2026-09-25 after the prediction above), verbatim output:
```
n=6400: x=12.852483, m*=29, CP_n mode=29, second-difference sign changes at a = [  14   45 6356 6387]
D2-P10 violations (n, x, m*, first bad a): []  count 0
```
Verdict: D2-P10 survives. At n = 6400 the full law is convex on [45, 6355] (2 m* = 58), and m* = 29 equals the CP_n mode. Together with the exact symmetry P(A_n = a) = P(A_n = n - a), convexity on [2m*, n-2m*] implies the center is the unique interior minimum on that range, for all tested n.

## 2026-09-25 D2-P11 (n = 10^6, large x): ERW mode versus CP_n mode and the refined mode law
Prediction: the exact mode of h at n = 10^6 is within 1 of the CP_n mode for x = 160 and within 2 for x = 320 (CP_n continuous modes 774.16 and 1772.00; refined heuristic law x log x + lambda0 x + (kappa1/2) log x + kappa0 with lambda0 = -0.222783, kappa1/2 = -0.535021, kappa0 = 0.549151 gives 774.23 and 1772.05).
Kill: |m*_ERW - m*_CP| > 1 at x = 160 or > 2 at x = 320.

### Outcome of D2-P11 (code/D2_bigx.py, run 2026-09-25 after the prediction above), verbatim output:
```
x=160.0: ERW mode 774 (continuous 773.661), CP_n mode 774; max|h/CP-1| on [1,3000] = 1.248e-02
x=320.0: ERW mode 1769 (continuous 1769.257), CP_n mode 1772; max|h/CP-1| on [1,3000] = 4.947e-02
```
Verdict: D2-P11 is REFUTED at x = 320 (ERW mode 1769, CP_n mode 1772, difference 3 > 2); it survives at x = 160. The ERW continuous mode sits below the CP_n continuous mode by 0.50 (x = 160) and 2.74 (x = 320), a finite-n shift that grows roughly like x^2 log x / n (0.13 and 0.59 here; ratio about -4). At the crossing (x ~ 2 log n, x^2/n -> 0) this shift is negligible, but the CP_n law is not a uniform-in-x proxy for the ERW mode when x^2/n is not small.

## 2026-09-25 D2-P12 (n = 2..9 at the exact crossing): endpoint dip for small n
Prediction: the endpoint dip P(A_n = n-1) > P(A_n = n) fails for n <= 5 and holds for n >= 8 (the sufficient condition x_n >= 2(1 - eps_n) first holds at n = 8); n = 6, 7 undecided by the theorem, predicted to hold (the exact ratio is about x_n/(2 - ...) plus the mirror term).
Kill: failure at n = 8 or 9, or the dip holding for some n <= 5.

### Outcome of D2-P12 (code/D2_smalln_dip.py, run 2026-09-25 after the prediction above), verbatim output:
```
n=2: x_n=0.666667, P(n-1)/P(n) = 1.000000, dip=False, sufficient cond x>=2(1-eps): False
n=3: x_n=0.878680, P(n-1)/P(n) = 1.000000, dip=False, sufficient cond x>=2(1-eps): False
n=4: x_n=1.071797, P(n-1)/P(n) = 1.049038, dip=True, sufficient cond x>=2(1-eps): False
n=5: x_n=1.226268, P(n-1)/P(n) = 1.081739, dip=True, sufficient cond x>=2(1-eps): False
n=6: x_n=1.378422, P(n-1)/P(n) = 1.138306, dip=True, sufficient cond x>=2(1-eps): False
n=7: x_n=1.502849, P(n-1)/P(n) = 1.176605, dip=True, sufficient cond x>=2(1-eps): False
n=8: x_n=1.630008, P(n-1)/P(n) = 1.229647, dip=True, sufficient cond x>=2(1-eps): True
n=9: x_n=1.735538, P(n-1)/P(n) = 1.267078, dip=True, sufficient cond x>=2(1-eps): True
```
Verdict: D2-P12 is REFUTED (the dip already holds at n = 4 and 5; I predicted failure for n <= 5). For n = 2, 3 the neighbour a = n-1 is a central value, so P(n-1) = P(center) = P(n) at the crossing and the ratio is exactly 1. The sufficient condition x_n >= 2(1 - eps_n) of Theorem 1 is loose at small n, where the mirror term h(n-1) and the lower bound x/(2(1-eps)) on the ratio are not accurate. Summary for the paper: at the crossing the endpoint is strictly below its neighbour for every n >= 4 (checked n <= 400; proved for n >= 8 given x_n >= 2(1-eps_n), which holds for all n >= 8 up to 400 and asymptotically since x_n ~ 2 log n).

## 2026-09-25 Correction after external verification (recorded, not a new prediction)
D2.md (Section 0 row Cj5 and Section 8) said Conjecture 5.1 (strict convexity of a -> P(A_n = a) on the closed range [2m*, n - 2m*]) was "verified for every n <= 400". That was an overstatement: D2-P10 only covered 100 <= n <= 400 and n = 6400, and n = 1600, 3200 were post hoc. A verifier pre-registered the missing range (their ledger code/D2_verify_ledger.md, item V9, prediction: closed-range convexity for every n in 10..99 and at n = 12800) and it was REFUTED on 10..99. Their output, verbatim (code/D2_verify_V9.py and the post hoc diagnostic D2_verify_V9diag.py):
```
V9(a) failures (n, x, m*, 2m*, n-2m*, #points, convex, argmin ok): [(10, 1.84551, 1, 2, 8, 7, False, np.True_), (11, 1.93786, 1, 2, 9, 8, False, True), (17, 2.42824, 2, 4, 13, 10, False, True), (18, 2.50136, 2, 4, 14, 11, False, np.True_), (19, 2.56489, 2, 4, 15, 12, False, True), (20, 2.63259, 2, 4, 16, 13, False, np.True_), (21, 2.69179, 2, 4, 17, 14, False, True), (22, 2.75486, 2, 4, 18, 15, False, np.True_), (30, 3.17566, 3, 6, 24, 19, False, np.True_), (31, 3.22027, 3, 6, 25, 20, False, True), (32, 3.26752, 3, 6, 26, 21, False, np.True_), (33, 3.31009, 3, 6, 27, 22, False, True), (34, 3.35512, 3, 6, 28, 23, False, np.True_), (35, 3.39584, 3, 6, 29, 24, False, True), (48, 3.87634, 4, 8, 40, 33, False, np.True_), (49, 3.90768, 4, 8, 41, 34, False, True), (50, 3.94049, 4, 8, 42, 35, False, np.True_), (51, 3.97085, 4, 8, 43, 36, False, True)]  count 18
V9(b) n=12800: x=14.158845 m*=33 range [66,12734] convex True center unique argmin True  (6.1s)
n=52: m*=5, nonconvex a in [2m*,n-2m*]: []; all sign changes of 2nd diff at a=[9, 44]
```
(In each of the 18 failures the only nonconvex points are the two endpoints a = 2m* and a = n - 2m*.) Consequence for D2.md: Conjecture 5.1 is restated on the open range [2m* + 1, n - 2m* - 1]; the closed-range version is recorded as refuted for n <= 51. The restated version is tested on new cells in D2-P13 below.

## 2026-09-25 D2-P13 (restated Conjecture 5.1, open range; new cells n = 401..600 and n = 25600)
Prediction: (a) for every n in 401..600, at its exact crossing x_n: the second difference of a -> P(A_n = a) is strictly positive at every a in [2m* + 1, n - 2m* - 1], and also at a = 2m* and a = n - 2m* (the closed-range failures stop at n = 51); the first difference on the upper half changes sign exactly once; P(A_n = a) > P(center) for every non-central 1 <= a <= n - 1 (center = n/2, or the two central values for odd n).
(b) n = 25600: x_25600 in [15.460, 15.470] (doubling increments 1.3062, 1.3057, 1.3063 give 15.465); upper-half mode m* = 38 (H1 with the pi_infinity residual interpolated at x = 15.47 gives continuous mode 37.77), equal to the CP_n mode; the full law is strictly convex on [2m*, n - 2m*]; the lower sign change a_1 above the bulk (the a where convexity resumes; 33, 39, 45, 51 at n = 1600, 3200, 6400, 12800) is in [55, 60]; the center is the unique interior minimiser; the endpoint ratio P(n-1)/P(n) lies in the Theorem 1 interval.
Kill: (a) any nonpositive second difference in [2m* + 1, n - 2m* - 1] for some n in 401..600 (kills the restated conjecture), or at a = 2m* or n - 2m* (kills only the closed-range add-on), or any other failure listed; (b) x_25600 outside the window, m* not in {37, 38} or not equal to the CP_n mode, any nonpositive second difference in [2m*, n - 2m*], a_1 outside [55, 60], or center not the unique interior minimiser.

## 2026-09-25 D2-P14 (the concave far-end stretch of h; tests the width guess that the verifier flagged)
Heuristic behind the prediction (written now): for r = n - m << n, h(n - r) is dominated by the first mark at vertex 2 (beta_2 uniform), giving h(n - r) ~ (x/n^2)[P(Y + 1 <= r) + 2r/n + 3r^2/n^2 + ...] with P(Y > r) ~ x/r. So h is concave in r from the inflection of the CDF part (r_lo ~ m_h + 1, m_h the mode of h) until the mirror curvature 6x/n^4 beats the deficit curvature 2x^2/(n^2 r^3), i.e. r_hi ~ (x n^2 / 3)^(1/3) = 0.693 (x n^2)^(1/3). Post hoc data so far: r_hi/(x n^2)^(1/3) = 201/297.0, 333/490.7, 896/1323.8 = 0.677, 0.679, 0.677 (n = 1600, 3200, 12800) and r_lo = m* + 1 in all three. The competing post hoc fit W = r_hi - r_lo + 1 ~ 0.72 n^(3/4) has no x-dependence.
Definition: in the far part m > n/2 the second difference of h (at m, using m-1, m, m+1) is negative exactly for r = n - m in [r_lo, r_hi].
Prediction: at (n, x) = (6400, 12.852483), (6400, 4), (6400, 40) and (25600, x_25600): (i) in m > n/2 the second difference of h has exactly one negative stretch; (ii) r_lo = m_h + 1 (kill if off by more than 2); (iii) r_hi/(x n^2)^(1/3) in [0.665, 0.695] at the two crossing cells (6400: r_hi in [537, 561]) and in [0.62, 0.72] at x = 4 and x = 40; (iv) r_hi(x = 40)/r_hi(x = 4) at n = 6400 in [1.9, 2.4] (the x^(1/3) law gives 2.154; an x-free n^(3/4) law gives about 1).
Kill: any of (i) to (iv) fails. (iv) failing near 1 would favour the n^(3/4) fit.

## 2026-09-25 D2-P15 (finite-n shift of the mode, ERW versus CP_n; tests the scaling guess the verifier flagged)
Definitions: m_c(law) = parabolic interpolation of log(law) through the integer argmax and its two neighbours (the D2_bigx.py definition), s(n, x) = m_c(h) - m_c(CP_n). Reported: s(10^6, 160) = -0.50, s(10^6, 320) = -2.74. Two guesses, calibrated on those two points: G1 (D2.md) s ~ -c x^2 log x / n with c in [3.8, 4.7]; G2 (nested-mark heuristic written now: a mark inside a marked subtree of size d flips back about d log d vertices, so the bulk loses about 2 eps x sum_{d <~ x log x} log d / d ~ x^2 log^2 x / n) s ~ -c' x^2 log^2 x / n with c' in [0.75, 0.81].
Calibration (reproduction, not a prediction): the same code at n = 10^6 must give ERW continuous modes 773.661 and 1769.257.
Prediction at n = 4 x 10^6, x = 160, 320, 640:
G1 windows: s in [-0.153, -0.123], [-0.694, -0.561], [-3.11, -2.51]; ratios s(320)/s(160) in [4.2, 4.9], s(640)/s(320) in [4.2, 4.8].
G2 windows: s in [-0.134, -0.124], [-0.690, -0.639], [-3.46, -3.21]; ratios in [4.8, 5.5] and [4.7, 5.4].
Kill: G1 is killed if any G1 window fails; G2 likewise. Both may die.

### Outcome of D2-P13 and D2-P14 (code/D2_p13_p14.py, run 2026-09-25 after the predictions above), verbatim output
Run 1 of part (a) (out/D2_p13_a_run1_buggy.txt). The script took the upper half as P[n//2:], which for odd n starts at the central value (n-1)/2, whose first difference to (n+1)/2 is exactly 0; so every odd n was reported with 2 sign changes and 1 zero. This is a script bug, not a property of the law:
```
D2-P13(a) n=401..600: open-range/shape failures [(401, 7.633878, 13, [], 2, 1, True, np.True_), (403, 7.643208, 13, [], 2, 1, True, np.True_), (405, 7.652491, 13, [], 2, 1, True, np.True_), (407, 7.66173, 13, [], 2, 1, True, np.True_), (409, 7.670925, 13, [], 2, 1, True, np.True_), (411, 7.680075, 13, [], 2, 1, True, np.True_), (413, 7.689181, 13, [], 2, 1, True, np.True_), (415, 7.698244, 13, [], 2, 1, True, np.True_), (417, 7.707264, 13, [], 2, 1, True, np.True_), (419, 7.716242, 13, [], 2, 1, True, np.True_)] count 100; closed-endpoint failures [] count 0  (t=11s)
   (n, m*, a_1, 2m*) samples: [(401, 13, 22, 26), (450, 14, 23, 28), (500, 14, 24, 28), (550, 15, 24, 30), (600, 15, 25, 30)] ; max a_1 - 2m* = -3
total time 10.85848617553711
```
Run 2 of part (a), after changing only that line to P[ceil(n/2):] (out/D2_p13_a.txt):
```
D2-P13(a) n=401..600: open-range/shape failures [] count 0; closed-endpoint failures [] count 0  (t=12s)
   (n, m*, a_1, 2m*) samples: [(401, 13, 22, 26), (450, 14, 23, 28), (500, 14, 24, 28), (550, 15, 24, 30), (600, 15, 25, 30)] ; max a_1 - 2m* = -3
total time 12.055010318756104
```
Part (b) and the n = 25600 cell of D2-P14 (out/D2_p13_n25600.txt; n even, so the bug did not affect it):
```
D2-P13(b) n=25600: x_n = 15.467209516  (t=9s)
   sum P = 0.999999999999995; m* = 38; mode of h = 38; CP_n mode = 38
   full-law second-difference sign changes at a = [19, 57, 25544, 25582]; a_1 = 57
   nonpositive sd in open range: []; at closed endpoints: []; first-diff sign changes on upper half 1 zeros 0; center unique interior min True
   P(n-1)/P(n) = 7.740620 in Theorem 1 interval [7.738280, 7.741829]: True
D2-P14 n=25600 x=15.467210: far-part negative runs (m) [[24138, 25561]]; m_h = 38; r_lo = 39; r_hi = 1462; r_hi/(x n^2)^(1/3) = 0.675538449822038; (x n^2)^(1/3) = 2164.2
total time 11.314375638961792
```
D2-P14 at n = 6400 (out/D2_p14_n6400.txt):
```
D2-P14 n=6400 x=12.852483: far-part negative runs (m) [[5853, 6370]]; m_h = 29; r_lo = 30; r_hi = 547; r_hi/(x n^2)^(1/3) = 0.6774412915249071; (x n^2)^(1/3) = 807.5; r_hi/n^0.75 = 0.7645
D2-P14 n=6400 x=4.0: far-part negative runs (m) [[6035, 6395]]; m_h = 4; r_lo = 5; r_hi = 365; r_hi/(x n^2)^(1/3) = 0.6670415465298103; (x n^2)^(1/3) = 547.2; r_hi/n^0.75 = 0.5101
D2-P14 n=6400 x=40.0: far-part negative runs (m) [[5561, 6262]]; m_h = 135; r_lo = 138; r_hi = 839; r_hi/(x n^2)^(1/3) = 0.7116863688509772; (x n^2)^(1/3) = 1178.9; r_hi/n^0.75 = 1.1725
   r_hi(40)/r_hi(4) = 2.2986
total time 0.18496227264404297
```
Verdicts. D2-P13 survives: (a) no failure for any n in 401..600, on the open range or at the closed endpoints (the inflection a_1 stays at least 3 below 2m*); (b) x_25600 = 15.467210 in [15.460, 15.470], m* = 38 = CP_n mode, convex on the closed range [76, 25524], a_1 = 57 in [55, 60], center the unique interior minimiser, endpoint ratio 7.7406 inside the Theorem 1 interval. D2-P14 survives: one negative stretch in every case; r_lo = m_h + 1 at the three crossing-type cells and at x = 4, r_lo = m_h + 3 at (6400, x = 40) (allowed: off by at most 2 from m_h + 1, exactly at the edge); r_hi/(x n^2)^(1/3) = 0.6774 (n = 6400), 0.6755 (n = 25600) in [0.665, 0.695], 0.6670 (x = 4) and 0.7117 (x = 40) in [0.62, 0.72]; r_hi(40)/r_hi(4) = 2.299 in [1.9, 2.4]. The x-free n^(3/4) fit is refuted by (iv) (it predicts a ratio near 1).

### Outcome of D2-P15 (code/D2_p15_modeshift.py, run 2026-09-25 after the prediction above), verbatim output (out/D2_p15_modeshift.txt):
```
n=1000000 x=160.0: ERW mode 774 (cont 773.6609); CP_n mode 774 (cont 774.1639); s = -0.5029; x^2 log x/n = 0.12992; x^2 log^2 x/n = 0.65939; c1 = 3.871; c2 = 0.763  (t=23s)
n=1000000 x=320.0: ERW mode 1769 (cont 1769.2572); CP_n mode 1772 (cont 1772.0026); s = -2.7454; x^2 log x/n = 0.59068; x^2 log^2 x/n = 3.40721; c1 = 4.648; c2 = 0.806  (t=23s)
n=4000000 x=160.0: ERW mode 774 (cont 774.0383); CP_n mode 774 (cont 774.1639); s = -0.1256; x^2 log x/n = 0.03248; x^2 log^2 x/n = 0.16485; c1 = 3.867; c2 = 0.762  (t=205s)
n=4000000 x=320.0: ERW mode 1771 (cont 1771.3157); CP_n mode 1772 (cont 1772.0026); s = -0.6870; x^2 log x/n = 0.14767; x^2 log^2 x/n = 0.85180; c1 = 4.652; c2 = 0.806  (t=205s)
n=4000000 x=640.0: ERW mode 3986 (cont 3986.2494); CP_n mode 3990 (cont 3989.8309); s = -3.5815; x^2 log x/n = 0.66165; x^2 log^2 x/n = 4.27526; c1 = 5.413; c2 = 0.838  (t=205s)
ratios at n=4e6: s(320)/s(160) = 5.469; s(640)/s(320) = 5.214
G1: windows [np.True_, np.True_, np.False_]; ratios [np.False_, np.False_]; survives: False
G2: windows [np.True_, np.True_, np.False_]; ratios [np.True_, np.True_]; survives: False
total time 204.86234998703003
```
Verdicts. Calibration reproduces (773.6609, 1769.2572). G1 (s ~ -c x^2 log x/n, the guess printed in D2.md) is REFUTED: the x = 640 window and both ratio windows fail (ratios 5.469 and 5.214). G2 (s ~ -c' x^2 log^2 x/n, c' in [0.75, 0.81]) is REFUTED: both ratios are inside their windows, but s(4e6, 640) = -3.5815 is outside [-3.46, -3.21] (c' = 0.838 there). What survives both kills: the 1/n scaling at fixed x is exact to the printed digits (s(4e6, 160)/s(1e6, 160) = 0.2498, s(4e6, 320)/s(1e6, 320) = 0.2502). Post hoc description (not a prediction): n s(n, x) = -502.4, -2748, -14326 at x = 160, 320, 640, local exponents 2.45 and 2.38 in x; c' = n|s|/(x^2 log^2 x) = 0.762, 0.806, 0.838, slowly increasing.

## 2026-09-25 Re-runs on already reported cells (checks of proved inequalities, not predictions)
code/D2_boundcheck.py was rewritten to test Theorem 1 and Theorem 3(a) exactly as printed (v1, which used a weaker e_2 and printed a weaker Theorem 1 upper bound, is kept as D2_boundcheck_v1_old.py), plus the explicit delta_ell now written into Theorem 3(c). Output (out/D2_boundcheck_v2.txt):
```
n=1600: Thm3(a) as printed: violations [] (count 0); e(m) < 1 exactly for m in [164, 400] (237 values)
    Thm1 as printed: [5.1533, 5.1828] contains exact 5.1699: True
    explicit delta_ell cumulative lower bound (m = 12..n/2): violations [] (count 0); delta_ell(n/2) = 28.383
n=3200: Thm3(a) as printed: violations [] (count 0); e(m) < 1 exactly for m in [118, 2215] (2098 values)
    Thm1 as printed: [5.7943, 5.8121] contains exact 5.8048: True
    explicit delta_ell cumulative lower bound (m = 12..n/2): violations [] (count 0); delta_ell(n/2) = 18.775
n=1e6 (m <= 1e4): violations 0 ; factor h m(m+1)/x vs bound factor 1-e at m=1000, 10000: 1.31636 0.78487 1.03777 0.97052
largest m with 4(m+2)e^{-(m-1)/9} >= 1: 48
n=1600: largest r with tau(r) >= 1: 294; 40 log n = 295
n=3200: largest r with tau(r) >= 1: 321; 40 log n = 323
n=1000000: largest r with tau(r) >= 1: 549; 40 log n = 553
```
No violation. At n = 1600 the printed bound of Theorem 3(a) is nontrivial (e < 1) only for 164 <= m <= 400, and the explicit delta_ell bound is vacuous at both sizes (delta_ell(n/2) = 28 and 19), so this part is a consistency check only. code/D2_llt_const2.py (corrected Theorem 4(a) constant and a numerical kappa for Theorem 4(c)), output (out/D2_llt_const2.txt):
```
|log u|/theta at theta = 1e-6, 1, 2, 3, pi: ['0.5', '0.50176253', '0.50739335', '0.51816366'] 0.5202519764
coefficient of |log theta| = 1/2 + pi/24 = 0.6308996939 ; constant (pi/2)(1/2+pi/24) + 0.53 = 1.521014922
max ratio on grid (theta in [1e-12, pi]): 0.75596664 at theta = 1.0e-12 ; ratio at 1e-12: 0.75596664 ; limit 1/(2*0.631) = 0.79239303
E_L: coefficient of log x/x = 99.643526 ; constant/x = 516.73079
f(l0) = 0.1806556338 ; f(l0)-f(l0-1) = 0.049474321 ; f(l0)-f(l0+1) = 0.026161038
inf over 0<|l-l0|<=1 of (f(l0)-f(l))/(l-l0)^2 on grid step 0.005: 0.026161038 at l-l0 = 1.0 ; -f''(l0)/2 = 0.039448335
kappa (numerical) = 0.026161
E_L(x) < kappa/2 requires x > 129231.0 ; at the crossing x ~ 2 log n, i.e. log n ~ 64615.4
```

Post hoc reproduction (not a prediction) of the verifier's V9 finding with my own engine (code/D2_repro_V9.py, reusing D2_p13_p14.py after adding an import guard; the crossing bracket is capped at 0.45 n for small n). Output (out/D2_repro_V9.txt):
```
closed-range endpoint failures: [10, 11, 17, 18, 19, 20, 21, 22, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51] 18
open-range failures: [] ; W-shape/argmin/Thm1 failures: []
```
The 18 closed-range failures reproduce exactly; the open-range statement, the W shape, the center as unique interior minimiser and Theorem 1 hold for every 10 <= n <= 99.

code/D2_effective.py (formula evaluation only: where the explicit Theorem 3(c) / Corollary 6.3 bounds become non-vacuous at the crossing, x from x + log x = 2 log n - log 8). Output (out/D2_effective.txt):
```
n=1e4: x=13.722; hypotheses False {'n1000': True, 'epsH': False, 'l0': True, 'floor': False}; Delta(n/2)=60.7; upper factor 1+3sqrt(Delta)=24.37; lower factor 1-e_2(n/2)=0.6741
n=1e5: x=18.053; hypotheses True ; Delta(n/2)=13.48; upper factor 1+3sqrt(Delta)=12.01; lower factor 1-e_2(n/2)=0.9471
n=1e6: x=22.441; hypotheses True ; Delta(n/2)=2.548; upper factor 1+3sqrt(Delta)=5.789; lower factor 1-e_2(n/2)=0.9922
n=1e7: x=26.866; hypotheses True ; Delta(n/2)=0.4323; upper factor 1+3sqrt(Delta)=2.973; lower factor 1-e_2(n/2)=0.9989
n=1e8: x=31.318; hypotheses True ; Delta(n/2)=0.06792; upper factor 1+3sqrt(Delta)=1.782; lower factor 1-e_2(n/2)=0.9999
n=1e8.5: x=33.551; hypotheses True ; Delta(n/2)=0.02632; upper factor 1+3sqrt(Delta)=1.487; lower factor 1-e_2(n/2)=0.9999
n=1e9: x=35.789; hypotheses True ; Delta(n/2)=0.01007; upper factor 1+3sqrt(Delta)=1.301; lower factor 1-e_2(n/2)=1
n=1e9.5: x=38.031; hypotheses True ; Delta(n/2)=0.003812; upper factor 1+3sqrt(Delta)=1.185; lower factor 1-e_2(n/2)=1
n=1e10: x=40.276; hypotheses True ; Delta(n/2)=0.001428; upper factor 1+3sqrt(Delta)=1.113; lower factor 1-e_2(n/2)=1
n=1e11: x=44.776; hypotheses True ; Delta(n/2)=0.0001954; upper factor 1+3sqrt(Delta)=1.042; lower factor 1-e_2(n/2)=1
n=1e12: x=49.285; hypotheses True ; Delta(n/2)=2.597e-05; upper factor 1+3sqrt(Delta)=1.015; lower factor 1-e_2(n/2)=1
n=1e14: x=58.327; hypotheses True ; Delta(n/2)=4.281e-07; upper factor 1+3sqrt(Delta)=1.002; lower factor 1-e_2(n/2)=1
Corollary 6.3 upper bound first applies (Delta(n/2) <= 1/16, all hypotheses) at n ~ 1.107e+08
Corollary 6.3 lower bound first non-trivial (e_2(n/2) < 1) at n ~ 2.195e+03
```
