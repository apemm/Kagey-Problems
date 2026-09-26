# Problem 131 Paper D, topic D4 (aging persistence): pre-registration ledger; predictions are written before the computation that tests them, outcomes appended verbatim below, refuted predictions never deleted.

Model for every entry: X_1 = +1 or -1 with probability 1/2 each; for k >= 2, X_k = -X_{k-1} with probability c/k (0 < c < 2), else X_k = X_{k-1}. S_n = number of k <= n with X_k = +1. Center bin m = n/2 (n even), end bin n. c_n = the value of c where P(S_n = n/2) = P(S_n = n). Predicted numbers below come from code/D4_predict.py (closed forms only; no exact law of S_n was computed before these entries were written).

## 2026-09-25, P1: exact law at c = 1

Prediction (proved by induction before any computation): at c = 1, for every n >= 2, P(S_n = s) = 1/n for 1 <= s <= n-1 and P(S_n = 0) = P(S_n = n) = 1/(2n). Jointly, given X_1 = +1: P(S_n = s, X_n = +) = (s-1)/(n(n-1)) and P(S_n = s, X_n = -) = (n-s)/(n(n-1)) for 1 <= s <= n-1, and P(S_n = n, X_n = +) = 1/n.
Kill: any mismatch in exact rational arithmetic for 2 <= n <= 60.

## 2026-09-25, P2: path weights and monotonicity

Prediction (proved): P(path) = (1/2) prod_{k=2}^n (1 - c/k) * prod_{t in switch set} c/(t - c). Hence R_{n,s}(c) = P(S_n = s)/P(S_n = n) is a polynomial with nonnegative coefficients in w_t = c/(t-c), strictly increasing in c on (0,2) for 1 <= s <= n-1; the crossing c_n is unique; c_n < 1 for all even n (because R_{n,s}(1) = 2); c_2 = 2/3.
Kill: brute-force enumeration (all 2^n paths, exact Fractions, n <= 14, c in {1/3, 1/2, 7/10, 1, 3/2}) disagrees with the transfer recursion; or R_{n,n/2}(c) fails to increase on a grid c = 0.01..1.99 (step 0.01) for n in {10, 50, 200}; or any computed c_n >= 1.

## 2026-09-25, P3: proved bracket for c_n

Prediction (proved): c^(n/2+1) <= c_n <= c^(n), where c^(N) is the root in (0,1) of N prod_{k=2}^N (1 - c/k) = 2c. Values: n=200: [0.887494097, 0.898783845]; n=800: [0.90815145, 0.915873355].
Kill (hard; would mean a proof or code error): any even n in 4..400, or n in {800, 1600, 3200}, with c_n outside its bracket.

## 2026-09-25, P4: sharp crossing values (the main pre-registered numbers)

Prediction: c_n is close to c*_n, the root of 4^{1-c}/(B(c,c) n) = (1/2) Gamma(n+1-c)/(Gamma(2-c) Gamma(n+1)); and c_n = 1 - log2/(L+g1) - (g2/2)(log 2)^2/(L+g1)^3 + O(L^{-4}) with L = log n, g1 = gamma + 2 - 2 log 2 = 1.19092, g2 = pi^2/2 - 4 = 0.93480.

| n | c*_n (predicted c_n) | asym1 | asym2 | tolerance on abs(c_n - c*_n) |
| --- | --- | --- | --- | --- |
| 50 | 0.862540833 | 0.864167207 | 0.86247724 | 5e-3 |
| 100 | 0.879346271 | 0.880411277 | 0.879257996 | 3e-3 |
| 200 | 0.892441685 | 0.893185131 | 0.892363343 | 2e-3 |
| 400 | 0.902949417 | 0.903493464 | 0.902887377 | 1e-3 |
| 800 | 0.911574859 | 0.911987268 | 0.91152754 | 5e-4 |
| 1600 | 0.91878571 | 0.919106891 | 0.918749948 | 3e-4 |
| 3200 | 0.924905328 | 0.925160862 | 0.924878211 | 2e-4 |

Kill: abs(c_n - c*_n) above the tolerance at n = 200 or n = 800 (the two pre-registered headline cells). Secondary (heuristic rate O(1/(n log n)) for c_n - c*_n): abs(c_n - c*_n) at n = 800 is at most half its value at n = 200; kill if not.
Program.md claim under test: "the crossing is at c = 1". Prediction: false at every finite n; c_n < 1 and 1 - c_n ~ log 2/log n, so c_n = 0.892 at n = 200 and 0.912 at n = 800.

## 2026-09-25, P5: local limit at the center

Prediction (proved for 0 < c < 2 with a slow rate; the numbers here test the heuristic O(1/n) rate): n P(S_n = n/2) -> f_c(1/2) = 4^{1-c}/B(c,c): 0.636619772 (c=0.5), 0.834626842 (c=0.75), 0.936873589 (c=0.9), 1 exactly for every n (c=1), 1.144139645 (c=1.25), 1.273239545 (c=1.5).
Kill: at n = 800 any abs(n P(S_n=n/2) - f_c(1/2)) > 0.01 for these c; or at c = 1 any n with n P(S_n = n/2) != 1 beyond 1e-12 relative; or the error fails to shrink by a factor >= 2 from n = 200 to n = 800 (heuristic rate).

## 2026-09-25, P6: shape at the crossing c = c_n

Prediction: (a) proved identity P(S_n = n-1)/P(S_n = n) = c(1+c)/(2-c) + c(1-c)/(n-c); at c = c_n this is about 1.525 (n=200) and 1.601 (n=800), so the end atom lies strictly below its neighbour. (b) Heuristic (Beta(c,c) is U-shaped for c < 1): the center m = n/2 is the unique minimum of P(S_n = s) over 1 <= s <= n-1; P(S_n = s) is strictly increasing in s on m <= s <= n-1; the global maxima are at s = 1 and s = n-1.
Kill: any of (b) fails at n = 200 or n = 800; or (a) disagrees with the exact law beyond 1e-10 relative.

## 2026-09-25, outcomes of P1 and P2 (code/D4_check_exact.py, verbatim output)

```
P2 brute/recursion/path-weight exact mismatches (n<=14, 5 values of c): 0
c=7/10, n=40: max rel err float=1.08e-15, dft abs err=1.11e-16
c=3/2, n=40: max rel err float=3.85e-16, dft abs err=7.29e-17
P1 failures for 2<=n<=60 (exact): 0
n=10: R_(n,n/2) strictly increasing on c=0.01..1.99: True; R at c=1: 2.000000000000000
n=50: R_(n,n/2) strictly increasing on c=0.01..1.99: True; R at c=1: 2.000000000000000
n=200: R_(n,n/2) strictly increasing on c=0.01..1.99: True; R at c=1: 1.999999999999999
n=2 at c=2/3: P(S=1) = 1/3  P(S=2) = 1/3
min over even n<=400 of log(P(center)/P(end)) at c=1: 0.6931471805599427 (log 2 = 0.6931471805599453 )
```
Verdict: P1 confirmed (exact, n <= 60). P2 confirmed (exact n <= 14; monotone on the grid; c_2 = 2/3; R = 2 at c = 1 so c_n < 1 for even n <= 400).

## 2026-09-25, outcomes of P3, P4, P5, P6 (code/D4_cross.py, verbatim output)

```
P3: bracket violations for even n in 4..400: none

P4: n, c_n (float engine), c_n (DFT engine), c*_n pred, c_n - c*_n, tol, in bracket?, (1-c_n) log n
   50  0.863081257448  0.863081257448  0.862540833  +5.404e-04  5e-03  PASS  True  0.535629
  100  0.879555975062  0.879555975062  0.879346271  +2.097e-04  3e-03  PASS  True  0.554665
  200  0.892525269532  0.892525269532  0.892441685  +8.358e-05  2e-03  PASS  True  0.569435
  400  0.902983482426  0.902983482426  0.902949417  +3.407e-05  1e-03  PASS  True  0.581271
  800  0.911589002819  0.911589002819  0.911574859  +1.414e-05  5e-04  PASS  True  0.590993
 1600  0.918791675222  0.918791675222  0.918785710  +5.965e-06  3e-04  PASS  True  0.599135
 3200  0.924907877897  nan  0.924905328  +2.550e-06  2e-04  PASS  True  0.606061
ratio |c_200-c*_200| / |c_800-c*_800| = 5.910 (needs >= 2)
exact n=200 at c = c_200 - 1e-6: P(center) - P(end) sign = -1
exact n=200 at c = c_200 + 1e-6: P(center) - P(end) sign = 1

P5: n*P(S_n=n/2) vs f_c(1/2) = 4^{1-c}/B(c,c)
  c= 0.5: f=0.636619772  err(200)=-1.590e-03  err(800)=-3.978e-04  err(3200)=-9.946e-05  ratio 200/800=3.996  n*err: -0.3179 -0.3182 -0.3183
  c=0.75: f=0.834626842  err(200)=-1.039e-03  err(800)=-2.605e-04  err(3200)=-6.519e-05  ratio 200/800=3.988  n*err: -0.2078 -0.2084 -0.2086
  c= 0.9: f=0.936873589  err(200)=-4.669e-04  err(800)=-1.170e-04  err(3200)=-2.927e-05  ratio 200/800=3.990  n*err: -0.0934 -0.0936 -0.0937
  c= 1.0: f=1.000000000  err(200)=+6.661e-16  err(800)=+1.998e-15  err(3200)=-2.109e-15  ratio 200/800=0.333  n*err: +0.0000 +0.0000 -0.0000
  c=1.25: f=1.144139645  err(200)=+1.429e-03  err(800)=+3.575e-04  err(3200)=+8.938e-05  ratio 200/800=3.998  n*err: +0.2859 +0.2860 +0.2860
  c= 1.5: f=1.273239545  err(200)=+3.187e-03  err(800)=+7.960e-04  err(3200)=+1.990e-04  ratio 200/800=4.004  n*err: +0.6374 +0.6368 +0.6367

P6: shape at the crossing
  n=200: c_n=0.892525270  R1 exact=1.5256873384  closed=1.5256873384  interior argmin=100 (m=100, unique=True)  increasing on [m,n-1]: True  argmax=1  P(center)/P(end)=1.000000000000
     P(n)=4.657533e-03 P(n-1)=7.105940e-03 P(n-2)=6.585441e-03 P(n-3)=6.306985e-03 P(n-10)=5.565452e-03 P(m)=4.657533e-03
  n=800: c_n=0.911589003  R1 exact=1.6011353178  closed=1.6011353178  interior argmin=400 (m=400, unique=True)  increasing on [m,n-1]: True  argmax=1  P(center)/P(end)=1.000000000000
     P(n)=1.180342e-03 P(n-1)=1.889887e-03 P(n-2)=1.773612e-03 P(n-3)=1.710842e-03 P(n-10)=1.539529e-03 P(m)=1.180342e-03
```
Verdict: P3 confirmed (no violations). P4 confirmed: c_200 = 0.8925253 (pred 0.8924417, diff 8.4e-5, tol 2e-3); c_800 = 0.9115890 (pred 0.9115749, diff 1.4e-5, tol 5e-4); two engines agree to 12 digits; exact rational sign check at n = 200 brackets c_200 within 1e-6; error ratio 5.9 >= 2. The program.md claim "crossing at c = 1" is refuted at every finite n (c_n < 1, (1 - c_n) log n = 0.57 at n = 200, slowly rising to log 2 = 0.693). P5 confirmed, error ratio about 4 per quadrupling (rate 1/n, faster than the heuristic threshold). P6 confirmed: end atom below its neighbour, center the unique interior minimum, profile increasing from m to n-1, argmax at s = 1 (and s = n-1 by symmetry).

## 2026-09-25, P7 (post hoc pattern, registered before testing on new cells)

Observation (not pre-registered; read off the P5 output above): n*err/f_c(1/2) equals c - 1 to 3 digits in every row, i.e. n P(S_n = n/2) = f_c(1/2) (1 + (c-1)/n + O(n^-2)).
Prediction on NEW cells: for c in {0.3, 0.6, 1.1, 1.8} and n in {100, 400, 1000}, the quantity n^2 (n P(S_n=n/2)/f_c(1/2) - 1 - (c-1)/n) stays bounded: its absolute value is below 5 at every cell, and its values at n = 400 and n = 1000 differ by less than 0.2 (so the next term is O(n^-2)).
Kill: any cell with absolute value >= 5, or a difference >= 0.2 between n = 400 and n = 1000 at some c.

## 2026-09-25, outcome of P7 (code/D4_p7.py, verbatim output)

```
c=0.3: n^2*(nP/f - 1 - (c-1)/n) at n=100,400,1000: -3.69068 -7.31973 -11.06944  |diff 400-1000|=3.7497  (engines rel. diff at n=1000: 3.0e-13)
c=0.6: n^2*(nP/f - 1 - (c-1)/n) at n=100,400,1000: +0.29716 +0.33274 +0.35096  |diff 400-1000|=0.0182  (engines rel. diff at n=1000: 7.3e-14)
c=1.1: n^2*(nP/f - 1 - (c-1)/n) at n=100,400,1000: -0.03523 -0.03505 -0.03502  |diff 400-1000|=0.0000  (engines rel. diff at n=1000: 4.1e-14)
c=1.8: n^2*(nP/f - 1 - (c-1)/n) at n=100,400,1000: +0.56321 +0.56080 +0.56032  |diff 400-1000|=0.0005  (engines rel. diff at n=1000: 3.3e-14)
```
Verdict: P7 REFUTED (killed at c = 0.3: |value| reaches 7.3 and 11.1 and the 400-to-1000 difference is 3.75). The (c-1)/n term survives at every c tested; what fails is the O(n^-2) remainder for small c. Post hoc reading: the c = 0.3 increments (3.63, 3.75) match n^{0.4} = n^{2-(1+2c)} increments (4.68, 4.86) with ratio 1.033 vs 1.038, suggesting a remainder term B(c) n^{-1-2c} (the n^{-2c} decay of the initial-condition memory); at c = 0.6 the slow drift is consistent with the same term. Not proved.

## 2026-09-25, P8: remainder exponent for small c

Prediction: for c in {0.2, 0.3}, E_n := n^{1+2c} (n P(S_n=n/2)/f_c(1/2) - 1 - (c-1)/n) converges to a negative constant; at n = 400, 1600, 6400 the values are negative and abs(E_6400/E_1600 - 1) < 0.10.
Kill: a positive value, or abs(E_6400/E_1600 - 1) >= 0.10 at either c.

## 2026-09-25, outcome of P8 (code/D4_p8.py, verbatim output)

```
c=0.2: E_400=-0.83042  E_1600=-0.85450  E_6400=-0.86445  |E_6400/E_1600-1|=0.0116
c=0.3: E_400=-0.66630  E_1600=-0.71064  E_6400=-0.73540  |E_6400/E_1600-1|=0.0348
```
Verdict: P8 confirmed (negative, stabilizing). Numerically n P(S_n=n/2) = f_c(1/2) [1 + (c-1)/n + B(c) n^{-1-2c} + ...] with B(0.2) about -0.87, B(0.3) about -0.75. Heuristic only; irrelevant at the crossing (c near 0.9, where n^{-1-2c} = n^{-2.8}).

## 2026-09-25, P9: effective-length predictor c**_n (post hoc idea, registered before new cells)

Idea (post hoc, from P5/P7): P(S_n = n/2) is close to f_c(1/2)/(n + 1 - c) (exact at c = 1). Define c**_n as the root of f_c(1/2)/(n+1-c) = (1/2) Gamma(n+1-c)/(Gamma(2-c)Gamma(n+1)) (code/D4_predict2.py). Retrospective (cells already known, NOT a test): c**_200 = 0.892525499368 vs c_200 = 0.892525269532 (diff 2.3e-7); c**_800 = 0.911589012426 vs c_800 = 0.911589002819 (diff 9.6e-9).
Prediction on NEW cells: c**_300 = 0.898899809493, c**_1000 = 0.914043475105, c**_5000 = 0.928380102785, with abs(c_n - c**_n) < 1e-6 (n=300), < 1e-7 (n=1000), < 1e-8 (n=5000), and c_n < c**_n in all three.
Kill: any tolerance exceeded, or the sign reversed.

## 2026-09-25, outcome of P9 (code/D4_p9.py, verbatim output)

```
n=300: c_n=0.8988997193688  c**_n=0.898899809493  c_n-c**_n=-9.012e-08  tol=1e-06  PASS  DFT engine c_n=0.8988997193688
n=1000: c_n=0.9140434693047  c**_n=0.914043475105  c_n-c**_n=-5.800e-09  tol=1e-07  PASS  DFT engine c_n=0.9140434693047
n=5000: c_n=0.9283801026263  c**_n=0.928380102785  c_n-c**_n=-1.587e-10  tol=1e-08  PASS
```
Verdict: P9 confirmed at all three new cells (sign and tolerance). The effective-length predictor is a numerical observation, not a theorem.

## 2026-09-25, P10: shape at the crossing for every small even n

Prediction: for every even n in 4..400, at c = c_n: (a) P(S_n = n-1) > P(S_n = n) (proved for n >= 6 from the bracket, since c^(4) > sqrt(3) - 1 and R1 > 1 there; n = 4 is not covered by the proof); (b) heuristic: the center is the unique minimum of P(S_n = s) over 1 <= s <= n-1, P(S_n = s) is strictly increasing on n/2 <= s <= n-1, and the maximum over all s is at s in {1, n-1}.
Kill: any even n in 4..400 where (a) or (b) fails.

## 2026-09-25, outcome of P10 (code/D4_p10.py, verbatim output)

```
n=4: c_n=0.7367009139  R1=1.072209 (closed 1.072209)  profile=[1.      1.07221 1.      1.07221 1.     ]
n=6: c_n=0.7688596457  R1=1.138643 (closed 1.138643)  profile=[1.      1.13864 1.02648 1.      1.02648 1.13864 1.     ]
n=8: c_n=0.7879160901  R1=1.185406 (closed 1.185406)  profile=[1.      1.18541 1.06105 1.01339 1.      1.01339 1.06105 1.18541 1.     ]
P10(a) failures: none
P10(b) failures: none
sqrt(3)-1 = 0.7320508075688772
```
Verdict: P10 confirmed for every even n in 4..400 (n = 4 holds with little room: c_4 = 0.73670 > sqrt(3) - 1 = 0.73205).

## 2026-09-25, P11: all-bin averaging bounds (proved; numerical check)

Prediction (proved): for every n >= 2 and 1 <= s <= n-1, P(S_n = s) = E[q_{tau,n}] for a random time tau in [j+1, n], j = min(s, n-s), where q_{t,n} = (c/t) prod_{k=t+1}^n (1 - c/k). Hence for c <= 1: c/n <= P(S_n = s) <= (c/(j+1)) prod_{k=j+2}^n (1 - c/k), and for c >= 1 the reverse. Consequence: if n prod_{k=2}^n (1-c/k) < 2c (c > c^(n)), the end atom is strictly below every interior bin.
Kill: any violation (relative slack 1e-12) for c in {0.5, 0.8, 0.95, 1.3, 1.7} and n in {10, 11, 200, 201}; or, at n = 200 and c = c^(200) + 1e-9 = 0.898783846, some interior bin <= P(S_n = n).

## 2026-09-25, outcome of P11 (code/D4_p11.py, verbatim output)

```
P11 bound violations: 0
n=200, c=0.898783846: P(end)=4.4939191900e-03  min interior=4.6780544462e-03  end strictly below all interior: True
```
Verdict: P11 confirmed.

## 2026-09-25, exploratory (not a prediction test): code/D4_symbolic.py

c_2 = 2/3 (root of 3c - 2); c_4 = 0.736700913929816 is the real root of c^3 - 5c^2 + 14c - 8; c_6 = 0.768859645706246 is a root of 5c^5 - 52c^4 + 271c^3 - 788c^2 + 1404c - 720. The joint law at n = 5 has irreducible quadratic factors in c (e.g. 3c^2 - 7c + 10), so there is no Pochhammer closed form for general c.

## 2026-09-25, P12: fixed first step (proved; numerical check)

Prediction (proved from P1's joint law and the path-weight monotonicity restricted to paths with x_1 = +1): conditional on X_1 = +1, every ratio P(S_n = s | X_1=+)/P(S_n = n | X_1=+), 1 <= s <= n-1, is strictly increasing in c and equals 1 at c = 1. So the fixed-start crossing is exactly c = 1 for every n and every bin; for c < 1 the + end is the strict global maximum over s in 1..n, for c > 1 the strict global minimum.
Kill: any violation for c in {0.9, 0.99, 1.01, 1.1} and n in {50, 51, 200}, or c = 1 giving max |n P(S_n = s | +) - 1| > 1e-12 over 1 <= s <= n at those n.

## 2026-09-25, outcome of P12 (code/D4_p12.py, verbatim output)

```
n=50, c=1: max|nP(S_n=s|+)-1| over 1..n = 8.9e-16, P(S_n=0|+) = 0.0
   c=0.9: P(end|+)=3.105950e-02  max interior=2.541232e-02  min interior=1.869979e-02  ok=True
   c=0.99: P(end|+)=2.091452e-02  max interior=2.050037e-02  min interior=1.987298e-02  ok=True
   c=1.01: P(end|+)=1.912236e-02  max interior=2.012639e-02  min interior=1.950868e-02  ok=True
   c=1.1: P(end|+)=1.267027e-02  max interior=2.123772e-02  min interior=1.548588e-02  ok=True
n=51, c=1: max|nP(S_n=s|+)-1| over 1..n = 8.9e-16, P(S_n=0|+) = 0.0
   c=0.9: P(end|+)=3.051139e-02  max interior=2.496386e-02  min interior=1.833347e-02  ok=True
   c=0.99: P(end|+)=2.050853e-02  max interior=2.010242e-02  min interior=1.948332e-02  ok=True
   c=1.01: P(end|+)=1.874367e-02  max interior=1.973176e-02  min interior=1.912233e-02  ok=True
   c=1.1: P(end|+)=1.239699e-02  max interior=2.082104e-02  min interior=1.515187e-02  ok=True
n=200, c=1: max|nP(S_n=s|+)-1| over 1..n = 2.7e-15, P(S_n=0|+) = 0.0
   c=0.9: P(end|+)=8.925541e-03  max interior=7.302715e-03  min interior=4.682022e-03  ok=True
   c=0.99: P(end|+)=5.302013e-03  max interior=5.197023e-03  min interior=4.968983e-03  ok=True
   c=1.01: P(end|+)=4.714417e-03  max interior=5.030853e-03  min interior=4.809657e-03  ok=True
   c=1.1: P(end|+)=2.755242e-03  max interior=5.301553e-03  min interior=3.367518e-03  ok=True
P12 violations: 0
```
Verdict: P12 confirmed. With the first step fixed, the crossing is exactly c = 1 for every n; the symmetric start moves it to c_n = 1 - log 2/(log n + 1.19) + ..., the log 2 being the factor 2 by which symmetrization halves the end atom but not the center.

## 2026-09-25, revision round (after two verifier reports). Entries P13 to P15 are written before the computations that test them.

Context: the verifiers found prior art (Englander-Volkov 2018; Englander-Volkov-Wang 2020, footnote 1 on p. 7: with p_1 = 1/2, p_2 = 1/3, p_3 = 1/4, ... the walk has an exactly discrete-uniform law for each N). While checking this I also read Dietz-Lippitt-Sethuraman (arXiv:1901.08135), Theorem 2.18: the limit-law moments of the I + G/n chain equal the finite-N occupation probabilities of the chain with kernels (I - G/j)^{-1}. For two states with G(1,2) = G(2,1) = c this kernel is I + G/(j + 2c), i.e. switch probability c/(k - 1 + 2c) at step k >= 2. Together with Dietz-Sethuraman Thm 1.4 (limit Beta(c,c)) this predicts an exact beta-binomial law at every N. I proved it directly by induction on the joint law (notes D4.md, Prop. 16) before running anything.

## 2026-09-25, P13: exact beta-binomial law for the convention c/(k-1+2c), and the exact discrete arcsine law of the c/k walk at c = 1/2

Prediction (proved by induction before computing): fair first step, switch probability c/(k-1+2c) at step k >= 2 (any c > 0). For every N >= 1 and 0 <= s <= N:
P(S_N = s, X_N = +) = (s/N) * C(N,s) (c)_s (c)_{N-s} / (2c)_N, so S_N ~ BetaBinomial(N; c, c) exactly.
Consequences predicted: (i) at c = 1/2 this convention coincides with the D4 model (switch probability c/k); so the D4 walk at c = 1/2 has P(S_n = s) = C(2s,s) C(2n-2s,n-s)/4^n exactly (discrete arcsine law) for every n. (ii) In the c/(k-1+2c) convention, P(S_N = s)/P(S_N = N) is strictly increasing in c for 1 <= s <= N-1 and equals 1 at c = 1, so the crossing is exactly c = 1 for every N and every bin.
Kill: any mismatch in exact rational arithmetic for the joint formula, N <= 40, c in {1/3, 1/2, 7/10, 1, 3/2, 5/2}; any mismatch of the D4 law at c = 1/2 with the discrete arcsine law for n <= 60; or, for N in {9, 30} and c in {9/10, 99/100, 101/100, 11/10}, any interior bin on the wrong side of the end atom (exact), or any bin != 1/(N+1) at c = 1.

## 2026-09-25, P14: convention b = 1 (switch probability c/(k+1)), all-bin crossing exactly c = 1

Prediction (proved: path weights w_t = c/(t+1-c) increasing in c; at c = 1 the law is uniform on {0..n}, by the index shift of Prop. 3): for n in {7, 20, 101} (exact rationals), at c = 1 every bin equals 1/(n+1); at c = 999/1000 the end atom P(S_n = n) is strictly larger than every interior bin; at c = 1001/1000 it is strictly smaller than every interior bin.
Kill: any violation.

## 2026-09-25, P15: general shift b (switch probability c/(k+b)), first-order crossing

Prediction (proved at first order in the revised notes, Prop. 14(c); the exact c = 1 values from the averaging identity): at c = 1, every interior bin equals 1/(n+b) exactly and the end atom equals (1+b)/(2(n+b)). The crossing c_n(b) satisfies (1 - c_n) log n -> g0 := log(2/(1+b)). Numbers from code/D4_fix_predict.py (closed forms only; no law computed):
Tested cells: b in {-1/2, 2}, n in {200, 800, 3200}, float64 positive-term forward recursion.
(a) sign: c_n < 1 for b = -1/2 and c_n > 1 for b = 2, at all three n.
(b) c*_n(b) := root of f_c(1/2)/n = (1/2) Gamma(2+b) Gamma(n+b+1-c)/(Gamma(2+b-c) Gamma(n+b+1)); |c_n - c*_n(b)| <= 5e-3 (n=200), 1.5e-3 (n=800), 5e-4 (n=3200).
(c) heuristic effective length: c**_n(b) := root of f_c(1/2)/(n+b+1-c) = same end atom; |c_n - c**_n(b)| <= 1e-4 (n=200), 1e-5 (n=800), 1e-6 (n=3200).
(d) |(1 - c_n)(log n + g1_b) - g0| <= 0.15|g0| at n = 200 and <= 0.10|g0| at n = 3200, where g1_b = -psi(1+b) + 2 - 2 log 2.
(e) n P(S_n = n/2) at n = 800: within 0.05 of f_c(1/2) for c in {0.7, 1.3}; at c = 1 equal to n/(n+b) to 1e-12 relative; at n = 200, c = 1, the end atom equals (1+b)/(2(n+b)) to 1e-12 relative.
Kill: any of (a), (b), (d), (e) fails. (c) is heuristic; its failure refutes only the effective-length guess n+b+1-c.

P15 predictor values (code/D4_fix_predict.py, verbatim output; run before any law for b != 0 was computed):
```
b=-0.5: g0=1.38629436112  g1=2.5772156649
   n=200: c*=0.8171906533218  c**=0.8169745591865  asym1=0.8239745353636
   n=800: c*=0.8459862630868  c**=0.8459370384791  asym1=0.850321723526
   n=3200: c*=0.8668922406889  c**=0.86688102242  asym1=0.869808554674
b=+2.0: g0=-0.405465108108  g1=-0.309078696218
   n=200: c*=1.079329362905  c**=1.081248107489  asym1=1.081267931823
   n=800: c*=1.063275227186  c**=1.063655301907  asym1=1.063597052373
   n=3200: c*=1.052205005006  c**=1.052283537718  asym1=1.052238356717
f_c(1/2) at c=0.7: 0.798149704981
f_c(1/2) at c=1.3: 1.17101767007
```

## 2026-09-25, outcomes of P13 and P14 (code/D4_fix_P13_P14.py, verbatim output)

```
P13 joint beta-binomial mismatches (N<=40, 6 values of c): 0
P13 D4 walk at c=1/2 vs discrete arcsine law, n<=60, mismatches: 0
P13 crossing-side violations (N in {9,30}): none
P14 n=7 c=999/1000: ok=True  min_s P(s)/P(n)=0.997678748  max=0.998144193
P14 n=7 c=1: ok=True  min_s P(s)/P(n)=1.000000000  max=1.000000000
P14 n=7 c=1001/1000: ok=True  min_s P(s)/P(n)=1.001858480  max=1.002326371
P14 n=20 c=999/1000: ok=True  min_s P(s)/P(n)=0.996745049  max=0.998051447
P14 n=20 c=1: ok=True  min_s P(s)/P(n)=1.000000000  max=1.000000000
P14 n=20 c=1001/1000: ok=True  min_s P(s)/P(n)=1.001951448  max=1.003265454
P14 n=101 c=999/1000: ok=True  min_s P(s)/P(n)=0.995190823  max=0.998011390
P14 n=101 c=1: ok=True  min_s P(s)/P(n)=1.000000000  max=1.000000000
P14 n=101 c=1001/1000: ok=True  min_s P(s)/P(n)=1.001991590  max=1.004832341
P14 violations: none
```
Verdict: P13 confirmed (0 mismatches, exact): the c/(k-1+2c) chain has the joint beta-binomial law for N <= 40 at six values of c; the D4 walk at c = 1/2 has exactly the discrete arcsine law for n <= 60; in the c/(k-1+2c) convention every interior bin is on the predicted side of the end atom at c = 1 -+ 1/100, 1/10 (N = 9, 30), and the law is uniform at c = 1. P14 confirmed: with switch probability c/(k+1) the law at c = 1 is uniform on {0..n} and the all-bin crossing is exactly c = 1 (n = 7, 20, 101, exact).

## 2026-09-25, outcome of P15 (code/D4_fix_P15.py, verbatim output)

```
b=-0.5 n=200: c_n=0.8169742507418  sign ok=True  c_n-c*=-2.164e-04 (tol 5.0e-03) PASS  c_n-c**=-3.084e-07 (tol 1.0e-04) PASS  (1-c_n)(L+g1)=1.441425 vs g0=1.386294 rel=0.0398 PASS
b=-0.5 n=800: c_n=0.8459370263811  sign ok=True  c_n-c*=-4.924e-05 (tol 1.5e-03) PASS  c_n-c**=-1.210e-08 (tol 1.0e-05) PASS  (1-c_n)(L+g1)=1.426905 vs g0=1.386294 rel=0.0293 
b=-0.5 n=3200: c_n=0.8668810219003  sign ok=True  c_n-c*=-1.122e-05 (tol 5.0e-04) PASS  c_n-c**=-5.197e-10 (tol 1.0e-06) PASS  (1-c_n)(L+g1)=1.417467 vs g0=1.386294 rel=0.0225 PASS
   (e) b=-0.5 n=800 c=0.7: n P(center) = 0.798349577  f_c(1/2) = 0.798149705  diff = +1.999e-04  PASS
   (e) b=-0.5 n=800 c=1.3: n P(center) = 1.172189856  f_c(1/2) = 1.171017670  diff = +1.172e-03  PASS
   (e) b=-0.5 n=800 c=1: n P(center)/(n/(n+b)) - 1 = -2.22e-16; max interior |P*(n+b) - 1| = 4.33e-15
   (e) b=-0.5 n=200 c=1: end atom / ((1+b)/(2(n+b))) - 1 = +2.22e-16
b=+2.0 n=200: c_n=1.0812470320686  sign ok=True  c_n-c*=+1.918e-03 (tol 5.0e-03) PASS  c_n-c**=-1.075e-06 (tol 1.0e-04) PASS  (1-c_n)(L+g1)=-0.405361 vs g0=-0.405465 rel=0.0003 PASS
b=+2.0 n=800: c_n=1.0636552575568  sign ok=True  c_n-c*=+3.800e-04 (tol 1.5e-03) PASS  c_n-c**=-4.435e-08 (tol 1.0e-05) PASS  (1-c_n)(L+g1)=-0.405836 vs g0=-0.405465 rel=0.0009 
b=+2.0 n=3200: c_n=1.0522835357713  sign ok=True  c_n-c*=+7.853e-05 (tol 5.0e-04) PASS  c_n-c**=-1.946e-09 (tol 1.0e-06) PASS  (1-c_n)(L+g1)=-0.405816 vs g0=-0.405465 rel=0.0009 PASS
   (e) b=+2.0 n=800 c=0.7: n P(center) = 0.795857481  f_c(1/2) = 0.798149705  diff = -2.292e-03  PASS
   (e) b=+2.0 n=800 c=1.3: n P(center) = 1.168535298  f_c(1/2) = 1.171017670  diff = -2.482e-03  PASS
   (e) b=+2.0 n=800 c=1: n P(center)/(n/(n+b)) - 1 = +8.88e-16; max interior |P*(n+b) - 1| = 5.77e-15
   (e) b=+2.0 n=200 c=1: end atom / ((1+b)/(2(n+b))) - 1 = +6.66e-16
P15 failures: none
```
Verdict: P15 confirmed in every part. (a) signs correct (c_n < 1 for b = -1/2, c_n > 1 for b = 2). (b) |c_n - c*_n(b)| well inside tolerance. (c) heuristic effective length n+b+1-c confirmed: |c_n - c**_n(b)| = 3.1e-7, 1.2e-8, 5.2e-10 (b = -1/2) and 1.1e-6, 4.4e-8, 1.9e-9 (b = 2), with c_n < c**_n in all six cells. (d) (1-c_n)(L+g1_b) within 4.0% (b=-1/2) and 0.03% (b=2) of g0 = log(2/(1+b)) at n = 200, within 2.3% and 0.09% at n = 3200. (e) local limit holds at n = 800 (differences 2e-4 to 2.5e-3); at c = 1 every interior bin equals 1/(n+b) and the end atom equals (1+b)/(2(n+b)) to 6e-15.
