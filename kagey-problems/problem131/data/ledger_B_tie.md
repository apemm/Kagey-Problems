# Ledger B_tie: the complete-graph tie, general start, Kirchhoff form of a_k (Paper B)

Predictions are written here before the code that tests them is run. Outcomes are appended
verbatim below, and nothing registered here is deleted. Notes: `research131/B_tie.md` (session
scratchpad). Prediction numbers: `predict_general_start.py` (formula evaluation only), output
`data/general_start_predictions.txt`. Test script: `verify_general_start.py`, output
`data/general_start_output.txt`.

Notation. d states, repeat probability p, switch probability r = (1-p)/(d-1) to each other
state, sigma = p - r, u = r/p, v = r/sigma, L = log N, T = N r (shared notation), z = N u = T/p.
Window coordinate (Paper B's): t = z - L + (1/2) log L. Start law mu. For a word, S^(a)_n(u) is
the run polynomial of words with counts n that start with state a, S_n = sum_a S^(a)_n, and
omega_a(n) = S^(a)_n / S_n.

Prior data I have seen before writing these predictions: Paper C's ledger_C5 (P6, P6') measured
the K_3, mu = (1/2,1/2,0) window at N = 1e6, ..., 1e20 (t_ve = -0.390915, t_ef = -0.369274 at
N = 1e6, and T (0.026050 - width) = 0.0546 post hoc). So N = 1e6 below is not a blind cell; the
blind cells are N = 90, 1002, 10002, 100002. Nothing else below has been computed before.

## 2026-09-26 T1 (Kirchhoff form of the constants; exact identities)
(a) exp(-(k-1) a_k) = D_k = k^{k+1/2}/(4 pi)^{(k-1)/2}, k = 2..7. Two evaluations (from a_k and
from D_k) agree to 1e-12 relative.
(b) For K_k with conductances c_ij = x_i x_j (x rational, positive), the weighted spanning-tree
sum tau equals prod_i x_i (sum_i x_i)^{k-2}, k = 2..7. Method 1: reduced Laplacian determinant
(exact Fractions). Method 2: explicit enumeration of all k^{k-2} labelled trees by Pruefer
decoding. Method 3 (target): the closed form. Prediction: all three equal exactly.
(c) Doob chain G_ij = x_j/x_i (i != j) with alpha_i = x_i^2/sum x^2. Its asymptotic occupation
covariance Gamma = D Z + Z^T D (Z the fundamental matrix, exact Fractions), Sigma = Gamma without
row and column 1. Prediction: det Sigma = 2^{k-1} (prod alpha)^2 / tau(c), c_ij = sqrt(alpha_i
alpha_j) = x_i x_j / sum x^2, exactly, k = 2..7 (x chosen so that sum x^2 need not be a square;
alpha and c are rational anyway).
(d) Paper B's D(alpha) = A^{k/2+1} (prod alpha)^{-3/4} (4 pi)^{-(k-1)/2} equals
A^2 (4 pi)^{-(k-1)/2} sqrt(tau(alpha)) / prod alpha, and equals A^2 det(2 pi Sigma_alpha)^{-1/2};
agreement to 1e-12 relative at 5 random alpha for each k = 2..7.
(e) Legendre check for K_k: the Hessian of I(alpha) = d - A^2 in the coordinates
(alpha_2..alpha_k) (central finite differences, step 1e-4) times det Sigma_alpha (exact formula)
has determinant 1 to 1e-6, 3 random alpha for k = 2..5.
(f) Mass identity: sum over n in Z_{>0}^k with |n| = N of S_n(u) equals
sum_{j=1}^k (-1)^{k-j} C(k,j) j (1+(j-1)u)^{N-1}, as polynomials, k = 2..4, N = k..9.
Method 1: S_n from brute-force enumeration of words. Method 2: the closed form. Exact.
Also D_k (2 pi)^{(k-1)/2} (det Sigma_k)^{1/2} = k for k = 2..7 (float, 1e-12).
(g) HKST reading check, K_3 unit conductances, start 1, local times l = (0.7, 1.1, 1.6): the
density from Huang-Kious-Sidoravicius-Tarres Theorem 1, summed over the 3 roots, the 3 x 3 = 9
oriented spanning trees rooted there and the currents a in the affine cycle lattice (|winding| <=
40), equals the run-count density e^{-2 sum l} sum_m W_1(m) prod l_i^{m_i-1}/(m_i-1)! (W_1(m) =
Smirnov words starting at 1, m_i <= 40). Prediction: relative agreement 1e-10.
Kill for T1: any exact identity fails, or a float agreement is worse than its stated tolerance.

## 2026-09-26 T2 (exact law with a general start)
(a) d = 3, mu = (1/2, 1/3, 1/6), p in {1/5, 1/2, 9/10}, N = 1..7: the refresh formula
P = sum_m (sum_i mu_i m_i) (M-1)!/prod m_i! r^{M-1} sigma^{N-M} prod C(n_i-1, m_i-1) equals
brute-force enumeration of all 3^N words, exactly (Fractions), for every bin. (Includes p = 1/5
< 1/d, where sigma < 0.)
(b) Balanced bins with k | N: P^mu(n) = (d mu(F)/k) P^unif(n) exactly (same cells, faces of size
2 and 3).
(c) omega_a from the refresh weights equals S^(a)_n/S_n from word enumeration (exact).
(d) Rounding, k = 2, balanced bin (h+1, h), u at the window (z = L - (1/2)log L + a_2): predicted
0 < omega_big - omega_small and N (omega_big - omega_small) in [0.40, 0.60] at N = 21, 201, 2001
(heuristic value 0.5(1 - 1/(4z))). Proved bound to be checked too:
omega_big - omega_small <= (2/h)(E_w M + E_w M^2).
(e) omega lemma, k = 2, alpha = (0.6, 0.4) (N = 2000, n = (1200, 800)), z = L - (1/2)log L:
|omega_1 - 0.550510| <= 0.01, and omega_1 < 0.550510 (heuristic sign from the 1/4 in
kappa ~ sqrt(ny) + 1/4).
Kill: (a)-(c) any mismatch; (d), (e) outside the stated ranges.

## 2026-09-26 T3 (crossings with a general start; d = 4, mu = (2/5, 3/10, 1/5, 1/10))
Case A: balanced bin of F = {1,2,3} (k = 3, 3 | N) against vertex 1. a_3(mu) = a_3 + (1/2)
log(3 mu_1/mu(F)) = -0.5132183455. Case B: balanced bin of F = {2,3} (k = 2, N even) against
vertex 4. a_2(mu) = a_2 + log(2 mu_4/mu(F)) = -1.3836465598.
Methods: (1) general-start refresh formula (floats with exact integer binomials) + bisection in u;
(2) start-resolved run formula S^(a) = sum_m E(m,a) prod C(n_i-1,m_i-1) u^{M-1} with E(m,a) the
number of Smirnov words with multiplicities m that start with a (exact integer DP), + bisection.
Predictions:
(i) Exact: the crossing equals the root of S_n(u) = k mu_i/mu(F) (4/3 in case A, 0.4 in case B),
S_n the start-free polynomial; methods (1), (2) and this root agree to 1e-10 relative.
(ii) N = k: z = 1.414213562373 (case A, N = 3) and z = 0.4 (case B, N = 2).
(iii) Along the tested N (multiples of k), u_N is strictly decreasing (z_N = N u_N increasing).
(iv) ahat_N := z_N + (1/2) log z_N - L - 1/(8 z_N) satisfies |ahat_N - a_k(mu)| <= 1/z^2 + z^2/N
at N = 300, 3000, 30000 (case A) and N = 200, 2000, 20000 (case B). Predicted z (implicit
second-order form): case A 4.469852, 6.570851, 8.726855; case B 3.347849, 5.397452, 7.527187.
Secondary (heuristic): ahat_N - a_k(mu) is close to ((k-1)/2) z^2/N (0.0666, 0.0144, 0.0025 in
case A; 0.0280, 0.0073, 0.0014 in case B), within 1/z^2.
Kill: (i), (ii) or (iv) fails.

## 2026-09-26 T4 (K_3, mu = (1/2,1/2,0): the edge window at finite N)
Lower end: balanced edge (N/2, N/2, 0) against vertex 1. Upper end: balanced edge against the
maximum over all bins with three positive counts. N in {90, 1002, 10002, 100002, 1000002}.
Predictions:
(i) Exact identity: the lower-end crossing is Paper A's center crossing, i.e. the root of the
binary center polynomial S_{(N/2,N/2)}(u) = 1 (1e-10 relative, three methods: general-start
refresh formula, 2-colour run formula, and at N = 90 a brute-force DP over all bins).
(ii) Second-order values (from the implicit equations z - L + (1/2) log z = a_2 + 1/(8z) and
= t_ef + 1/(12z); the 1/12 is 1/8 minus the maximiser shift 1/24):
 N=90      t_low=-0.298226 t_up=-0.286088 width=0.012138
 N=1002    t_low=-0.340235 t_up=-0.323179 width=0.017057
 N=10002   t_low=-0.363991 t_up=-0.344597 width=0.019393
 N=100002  t_low=-0.379849 t_up=-0.359060 width=0.020789
 N=1000002 t_low=-0.391213 t_up=-0.369503 width=0.021710
Tolerance on each of t_low, t_up: 0.5/z^2 + z^2/N (0.174, 0.047, 0.014, 0.0061, 0.0036).
(iii) The window is nonempty at every tested N, including N = 90 (width > 0), and at N = 90 the
brute-force DP over all bins shows the global-mode sequence vertices {(90,0,0),(0,90,0)} ->
(45,45,0) -> a bin with three positive counts, with no other bin ever a global mode.
(iv) Maximiser shift (new, from gamma^T Sigma gamma / 2 = 1/24): at the upper end the full-face
maximiser has |n1 - n2| <= 1 and z (1/3 - n3/N) in [0.08, 0.14] at N >= 10002 (limit 1/9 =
0.111); predicted n3 ~ 3190.7, 32215.3, 324176.3 at N = 10002, 100002, 1000002.
(v) z log(M_full / P(N/3,N/3,N/3)) at the upper end lies in [0.030, 0.055] at N >= 10002
(limit 1/24 = 0.0417).
(vi) Discriminating: the no-shift width predictions (0.024431, 0.024778, 0.025005 at N = 10002,
100002, 1000002) are further from the measured widths than the shifted ones.
Kill: (i) mismatch, any t outside its tolerance, (iii) fails, (iv) or (v) outside range at any
N >= 10002, or (vi) fails at two of the three largest N.

## 2026-09-26 Outcomes of T1-T4 (verify_general_start.py)
Run history: run 1 stopped in T3 at N = 300 with an OverflowError while evaluating the M1 series at the
bisection bracket end u = 0.99 (y**(M-k) overflow); run 2 stopped at the same place because the truncated
series is not valid at u = 0.99 (both bracket values negative). Fixes: log-sum-exp evaluation and a bracket
[0.3 z_g/N, 2 z_g/N] for N > 60. No prediction was changed. The T1, T2 and T3 (N <= 30) lines printed by
runs 1 and 2 are identical to run 3. Verbatim output of run 3:

```
==========================================================================================
T1  Kirchhoff form of the constants
------------------------------------------------------------------------------------------
(a) exp(-(k-1)a_k) against D_k = k^{k+1/2}/(4pi)^{(k-1)/2}
   k=2  a_k=-0.467355827915  D_k=1.595769121606  exp(-(k-1)a_k)=1.595769121606  D_k/k^{k-2}=1.595769 (= k^{5/2}(4pi)^{-(k-1)/2} = 1.595769)
   k=3  a_k=-0.657059381685  D_k=3.721470044097  exp(-(k-1)a_k)=3.721470044097  D_k/k^{k-2}=1.240490 (= k^{5/2}(4pi)^{-(k-1)/2} = 1.240490)
   k=4  a_k=-0.813929418195  D_k=11.493575816011  exp(-(k-1)a_k)=11.493575816011  D_k/k^{k-2}=0.718348 (= k^{5/2}(4pi)^{-(k-1)/2} = 0.718348)
   k=5  a_k=-0.947465006112  D_k=44.250205895509  exp(-(k-1)a_k)=44.250205895509  D_k/k^{k-2}=0.354002 (= k^{5/2}(4pi)^{-(k-1)/2} = 0.354002)
   k=6  a_k=-1.063775186512  D_k=204.154269799753  exp(-(k-1)a_k)=204.154269799753  D_k/k^{k-2}=0.157526 (= k^{5/2}(4pi)^{-(k-1)/2} = 0.157526)
   k=7  a_k=-1.166875562834  D_k=1098.008514954393  exp(-(k-1)a_k)=1098.008514954392  D_k/k^{k-2}=0.065330 (= k^{5/2}(4pi)^{-(k-1)/2} = 0.065330)
   worst relative difference 1.44e-15
(b) tau(K_k, c_ij = x_i x_j): matrix-tree vs Pruefer enumeration vs prod x (sum x)^{k-2}
   k=2: matrix-tree==Pruefer: True   ==closed form: True   unit-weight count 1 (k^(k-2) = 1)  trees enumerated 1
   k=3: matrix-tree==Pruefer: True   ==closed form: True   unit-weight count 3 (k^(k-2) = 3)  trees enumerated 3
   k=4: matrix-tree==Pruefer: True   ==closed form: True   unit-weight count 16 (k^(k-2) = 16)  trees enumerated 16
   k=5: matrix-tree==Pruefer: True   ==closed form: True   unit-weight count 125 (k^(k-2) = 125)  trees enumerated 125
   k=6: matrix-tree==Pruefer: True   ==closed form: True   unit-weight count 1296 (k^(k-2) = 1296)  trees enumerated 1296
   k=7: matrix-tree==Pruefer: True   ==closed form: True   unit-weight count 16807 (k^(k-2) = 16807)  trees enumerated 16807
(c) det Sigma(Doob chain) == 2^{k-1} (prod alpha)^2 / tau(sqrt(alpha_i alpha_j)), exact
   k=2: equal: True   det Sigma = 1.022403e-01
   k=3: equal: True   det Sigma = 3.823869e-03
   k=4: equal: True   det Sigma = 7.301111e-05
   k=5: equal: True   det Sigma = 8.520625e-07
   k=6: equal: True   det Sigma = 6.741339e-09
   k=7: equal: True   det Sigma = 3.865846e-11
   center of K_k (x all equal): det Sigma_k == 2^{k-1} k^{1-2k}:
      k=2: True
      k=3: True
      k=4: True
      k=5: True
      k=6: True
      k=7: True
(d) D(alpha): Paper B's form vs A^2 (4pi)^{-(k-1)/2} sqrt(tau)/prod alpha vs A^2 det(2 pi Sigma)^{-1/2}
   35 random alpha: worst rel diff tree form 4.44e-16, covariance form 4.44e-16
(e) Legendre check: det Hess_{alpha'} (d - A^2) * det Sigma_alpha = 1
   k=2 alpha=[0.5701, 0.4299]: product = 1.000000045
   k=2 alpha=[0.7642, 0.2358]: product = 1.000000161
   k=2 alpha=[0.2795, 0.7205]: product = 1.000000108
   k=3 alpha=[0.2376, 0.3812, 0.3812]: product = 1.000000232
   k=3 alpha=[0.2776, 0.4513, 0.2711]: product = 1.000000242
   k=3 alpha=[0.2136, 0.4296, 0.3568]: product = 1.000000277
   k=4 alpha=[0.155, 0.2682, 0.3778, 0.1991]: product = 1.000000808
   k=4 alpha=[0.3298, 0.3807, 0.0943, 0.1952]: product = 1.000001589
   k=4 alpha=[0.3418, 0.2947, 0.1194, 0.2441]: product = 1.000001031
   k=5 alpha=[0.0674, 0.2435, 0.0778, 0.4164, 0.1949]: product = 1.000004791
   k=5 alpha=[0.0989, 0.3268, 0.2531, 0.0989, 0.2224]: product = 1.000002617
   k=5 alpha=[0.2077, 0.2519, 0.1175, 0.1709, 0.2519]: product = 1.000001581
   worst |product - 1| = 4.79e-06
(f) mass identity sum_n S_n(u) = sum_j (-1)^{k-j} C(k,j) j (1+(j-1)u)^{N-1}
   brute force (all k^N words) == closed form for k=2..4, N=k..9: True
   D_k (2pi)^{(k-1)/2} sqrt(det Sigma_k) / k - 1: worst 2.22e-16 (k=2..7)
(g) Huang-Kious-Sidoravicius-Tarres Theorem 1 (last-exit trees) vs run-count density, K_3
   HKST density = 2.267044696412719e-01   run-count density = 2.267044696412715e-01   rel diff = 1.78e-15
==========================================================================================
T2  exact law with a general start
------------------------------------------------------------------------------------------
(a) refresh formula == enumeration for 357 bins (d=3, mu=(1/2,1/3,1/6), p in {1/5,1/2,9/10}, N=1..7): True
(b) balanced bins, k | N: P^mu == (d mu(F)/k) P^unif exactly: True
(c) omega_a = E_w[m_a/M] (refresh weights) == S^(a)/S (enumeration): True
(d) rounding, k=2, bin (h+1,h) at t=0 (z = L - (1/2) log L + a_2)
   N=21: omega_big (refresh)=0.510776942328839 (run)=0.510776942328839  N(omega_big-omega_small)=0.452632  proved bound (2/h)(EM+EM^2)=6.6374e+00  diff<=bound: True  heuristic 0.5(1-1/(4z))=0.4381
   N=201: omega_big (refresh)=0.501175729929270 (run)=0.501175729929269  N(omega_big-omega_small)=0.472643  proved bound (2/h)(EM+EM^2)=2.0782e+00  diff<=bound: True  heuristic 0.5(1-1/(4z))=0.4688
   N=2001: omega_big (refresh)=0.500119701338405 (run)=0.500119701338406  N(omega_big-omega_small)=0.479045  proved bound (2/h)(EM+EM^2)=4.2795e-01  diff<=bound: True  heuristic 0.5(1-1/(4z))=0.4796
(e) omega lemma, k=2, n=(1200,800), N=2000, z = L - (1/2) log L
   omega_1 (run)=0.548555167907 (refresh)=0.548555167907  limit sqrt(a1)/A=0.550510  diff=-0.00196  heuristic (1-2 sqrt(a1)/A)/(4A^2 z)=-0.00194
==========================================================================================
T3  crossings with a general start, d=4, mu=(2/5,3/10,1/5,1/10)
------------------------------------------------------------------------------------------
A: F={1,2,3} (k=3) vs vertex 1: a_k(mu)=-0.5132183455, identity target S_n = 1.3333333333
   N=     3: z(M1)=1.414213562373 z(M2)=1.414213562373 z(S_n=target)=1.414213562373  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  DP(M3) ratio at root = 1.00000000000000
   N=    30: z(M1)=2.766346584059 z(M2)=2.766346584059 z(S_n=target)=2.766346584059  rel M1-M2=5.6e-16 M1-id=5.6e-16 trunc=0.0e+00  DP(M3) ratio at root = 1.00000000000000  u decreasing: True
            ahat=-0.171273  ahat-a(mu)=+0.341945  tol=0.38576  within: True  heuristic ((k-1)/2)z^2/N=0.25509  [0.0s]
   N=   300: z(M1)=4.548612647817 z(M2)=4.548612647817 z(S_n=target)=4.548612647817  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  u decreasing: True
            ahat=-0.425240  ahat-a(mu)=+0.087979  tol=0.11730  within: True  heuristic ((k-1)/2)z^2/N=0.06897  [0.3s]
   N=  3000: z(M1)=6.587380843338 z(M2)=6.587380843338 z(S_n=target)=6.587380843338  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  u decreasing: True
            ahat=-0.495384  ahat-a(mu)=+0.017834  tol=0.03751  within: True  heuristic ((k-1)/2)z^2/N=0.01446  [0.5s]
   N= 30000: z(M1)=8.729940847731 z(M2)=8.729940847731 z(S_n=target)=8.729940847731  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  u decreasing: True
            ahat=-0.509951  ahat-a(mu)=+0.003267  tol=0.01566  within: True  heuristic ((k-1)/2)z^2/N=0.00254  [0.9s]
B: F={2,3} (k=2) vs vertex 4: a_k(mu)=-1.3836465598, identity target S_n = 0.4000000000
   N=     2: z(M1)=0.400000000000 z(M2)=0.400000000000 z(S_n=target)=0.400000000000  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  DP(M3) ratio at root = 1.00000000000000
   N=    20: z(M1)=1.609752870433 z(M2)=1.609752870433 z(S_n=target)=1.609752870433  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  DP(M3) ratio at root = 1.00000000000000  u decreasing: True
            ahat=-1.225591  ahat-a(mu)=+0.158056  tol=0.51547  within: True  heuristic ((k-1)/2)z^2/N=0.06478  [0.0s]
   N=   200: z(M1)=3.389841688015 z(M2)=3.389841688015 z(S_n=target)=3.389841688015  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  u decreasing: True
            ahat=-1.334959  ahat-a(mu)=+0.048688  tol=0.14448  within: True  heuristic ((k-1)/2)z^2/N=0.02873  [0.0s]
   N=  2000: z(M1)=5.407675912958 z(M2)=5.407675912958 z(S_n=target)=5.407675912958  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  u decreasing: True
            ahat=-1.372432  ahat-a(mu)=+0.011214  tol=0.04882  within: True  heuristic ((k-1)/2)z^2/N=0.00731  [0.0s]
   N= 20000: z(M1)=7.529427709195 z(M2)=7.529427709195 z(S_n=target)=7.529427709195  rel M1-M2=0.0e+00 M1-id=0.0e+00 trunc=0.0e+00  u decreasing: True
            ahat=-1.381252  ahat-a(mu)=+0.002395  tol=0.02047  within: True  heuristic ((k-1)/2)z^2/N=0.00142  [0.0s]
==========================================================================================
T4  K_3, mu=(1/2,1/2,0): edge window at finite N
------------------------------------------------------------------------------------------
N=90: t_low(M1)=-0.20298836 t_low(A's S_N=1, M2)=-0.20298836 rel u diff=0.0e+00
        t_up=-0.04735056  width=0.155638   predicted t_low=-0.298226 t_up=-0.286088 width=0.012138
        t_low-pred=+0.095238 (tol 0.1794, ok True)  t_up-pred=+0.238737 (tol 0.1887, ok False)
        full-face maximiser at t_up: n=(32,32,26)  |n1-n2|=0  z(1/3-n3/N)=0.16446 (pred n3~27.3)
        z*log(M_full/P(N/3,N/3,N/3))=0.05386 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=2.7e-15  [0.1s]
N=1002: t_low(M1)=-0.31970797 t_low(A's S_N=1, M2)=-0.31970797 rel u diff=0.0e+00
        t_up=-0.27171620  width=0.047992   predicted t_low=-0.340235 t_up=-0.323179 width=0.017057
        t_low-pred=+0.020527 (tol 0.0474, ok True)  t_up-pred=+0.051463 (tol 0.0476, ok False)
        full-face maximiser at t_up: n=(345,345,312)  |n1-n2|=0  z(1/3-n3/N)=0.12453 (pred n3~314.4)
        z*log(M_full/P(N/3,N/3,N/3))=0.04640 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=0.0e+00  [0.1s]
N=10002: t_low(M1)=-0.35992716 t_low(A's S_N=1, M2)=-0.35992716 rel u diff=0.0e+00
        t_up=-0.33503444  width=0.024893   predicted t_low=-0.363991 t_up=-0.344597 width=0.019393
        t_low-pred=+0.004064 (tol 0.0143, ok True)  t_up-pred=+0.009563 (tol 0.0143, ok True)
        |width-shifted pred|=0.005500  |width-noshift pred|=0.000462  shifted closer: False
        full-face maximiser at t_up: n=(3413,3413,3176)  |n1-n2|=0  z(1/3-n3/N)=0.12267 (pred n3~3190.9)
        z*log(M_full/P(N/3,N/3,N/3))=0.04458 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=1.8e-15  [0.3s]
N=100002: t_low(M1)=-0.37896510 t_low(A's S_N=1, M2)=-0.37896510 rel u diff=0.0e+00
        t_up=-0.35751150  width=0.021454   predicted t_low=-0.379849 t_up=-0.359060 width=0.020789
        t_low-pred=+0.000884 (tol 0.0061, ok True)  t_up-pred=+0.001549 (tol 0.0061, ok True)
        |width-shifted pred|=0.000665  |width-noshift pred|=0.003324  shifted closer: True
        full-face maximiser at t_up: n=(33936,33936,32130)  |n1-n2|=0  z(1/3-n3/N)=0.11960 (pred n3~32215.5)
        z*log(M_full/P(N/3,N/3,N/3))=0.04385 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=0.0e+00  [0.6s]
N=1000002: t_low(M1)=-0.39091547 t_low(A's S_N=1, M2)=-0.39091547 rel u diff=0.0e+00
        t_up=-0.36927390  width=0.021642   predicted t_low=-0.391213 t_up=-0.369503 width=0.021710
        t_low-pred=+0.000298 (tol 0.0036, ok True)  t_up-pred=+0.000229 (tol 0.0035, ok True)
        |width-shifted pred|=0.000068  |width-noshift pred|=0.003363  shifted closer: True
        full-face maximiser at t_up: n=(338194,338194,323614)  |n1-n2|=0  z(1/3-n3/N)=0.11794 (pred n3~324176.5)
        z*log(M_full/P(N/3,N/3,N/3))=0.04343 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=1.1e-14  [1.2s]
N=90 brute-force DP over all bins (M3):
   DP vs M1 on 6 bins at t=-0.3: worst rel diff 6.7e-15; total mass 1.000000000000000
   from t=-1.00: global modes [(0, 90, 0), (90, 0, 0)]
   from t=-0.20: global modes [(45, 45, 0)]
   from t=-0.04: global modes [(32, 32, 26)]
   from t=+0.20: global modes [(31, 32, 27), (32, 31, 27)]
total time 15.6s
```

### Verdicts (written after reading the output above)
- T1 survives. (a) worst 1.4e-15. (b) matrix-tree = Pruefer enumeration = prod x (sum x)^{k-2}
  exactly for k = 2..7, and the unit-weight counts are 1, 3, 16, 125, 1296, 16807 = k^{k-2}.
  (c) det Sigma = 2^{k-1}(prod alpha)^2/tau exactly, k = 2..7, and 2^{k-1}k^{1-2k} at the center.
  (d) 4.4e-16 for both forms. (e) worst 4.8e-6 (tolerance 1e-6 was for the product; the
  registered tolerance is "to 1e-6": the k = 5 values 4.8e-6, 2.6e-6, 1.6e-6 and one k = 4 value
  1.6e-6 EXCEED it). So T1(e) as registered is KILLED on tolerance. Diagnosis: central finite
  differences with step 1e-4 on alpha as small as 0.067 have truncation error of relative size
  about (h/alpha_min)^2 ~ 2e-6; the product drifts upward with k exactly as that error does. This
  is a precision failure of the check, not of the identity (which (c) proves exactly and which is
  Legendre duality, C5 Prop 4(a)); it is not retested here because (c) and (d) already cover the
  statement used in the notes. (f) exact; 2.2e-16. (g) HKST vs run-count density 1.8e-15.
- T2 survives. (a)-(c) exact on 357 bins. (d) N(omega_big - omega_small) = 0.4526, 0.4726,
  0.4790 in [0.40, 0.60]; below the proved bound. (e) omega_1 - 0.550510 = -0.00196 (within
  0.01, and negative as predicted; the heuristic value was -0.00194).
- T3 survives. (i) M1 = M2 = root of S_n = target to <= 5.6e-16 at every N; (ii) exact at N = k;
  (iii) monotone; (iv) ahat - a(mu) = +0.0880, +0.0178, +0.0033 (case A, N = 300, 3000, 30000)
  and +0.0487, +0.0112, +0.0024 (case B, N = 200, 2000, 20000), all within tolerance; the
  heuristic ((k-1)/2) z^2/N accounts for most of each residual.
- T4 is KILLED by (ii): t_up - prediction = +0.2387 at N = 90 (tolerance 0.1887) and +0.0515 at
  N = 1002 (tolerance 0.0476). All other parts survive: (i) exact (0 relative difference);
  t_low within tolerance at every N and t_up within tolerance at N >= 10002; (iii) the DP at
  N = 90 shows vertices -> (45,45,0) -> (32,32,26) -> (31,32,27)/(32,31,27), no other bin, and
  its transition cells (-0.22,-0.20] and (-0.06,-0.04] contain the M1 values -0.20299, -0.04735;
  (iv) |n1-n2| = 0 and z(1/3 - n3/N) = 0.1227, 0.1196, 0.1179 (in [0.08, 0.14], tending to 1/9);
  (v) z log(M_full/P_bal) = 0.0446, 0.0439, 0.0434 (in [0.030, 0.055], tending to 1/24);
  (vi) the shifted width is closer at N = 100002 and 1000002 but not at 10002 (one failure of
  three; the kill condition needed two).
  Diagnosis (after the run). The second-order equations omit the discrete terms. The balanced
  k-face bin satisfies log S_n = ... - ((k-1)^2/2) z^2/N + O(z/N) (exponent (k - 1/2) z^2/N from
  k^2 x + (N-1) log(1-u) - (k-1) z, minus the run-length deficit k^2 z^2/(2N)). This is 1/2 z^2/N
  for the edge and 2 z^2/N for the full face, so the upper end moves by +(3/2) z^2/N and the lower
  end by +(1/2) z^2/N. Post hoc: (3/2) z^2/N = 0.200, 0.047, 0.0090, 0.00148, 0.00022 against the
  observed t_up residuals 0.239, 0.051, 0.0096, 0.00155, 0.00023. The same term explains T3's
  residuals. The width at N = 10002 is dominated by this term, which is why (vi) failed there.
  The kill stands. A corrected test on new cells is registered as T4'.

## 2026-09-26 T4' (new cells; registered after T4 was killed, before any code for it runs)
Same model and code path as T4 (M1 for the crossings, M2 for the sign confirmation), N in
{3000, 30000, 300000}. Predicted values from the equations with the discrete terms
(predict_general_start.py, section T4'):
 lower: z - L + (1/2) log z = a_2 + 1/(8z) + (1/2) z^2/N
 upper: z - L + (1/2) log z = t_ef + 1/(12z) + (3/2) z^2/N
 N=3000    t_low=-0.346109  t_up=-0.314003  width=0.032106  (noshift width 0.037953)
 N=30000   t_low=-0.371064  t_up=-0.348481  width=0.022582  (noshift width 0.027062)
 N=300000  t_low=-0.385511  t_up=-0.363855  width=0.021656  (noshift width 0.025283)
Tolerance on t_low and t_up: 0.2/z^2 + 3z/N (0.0112, 0.0035, 0.0018).
Also: the shifted width (1/12) is closer than the noshift width (1/8) at all three N; the
maximiser has |n1 - n2| <= 1 and z(1/3 - n3/N) in [0.09, 0.13]; z log(M_full/P_bal) in
[0.035, 0.050].
Kill: any value outside its tolerance or range at any of the three N.

### T4' outcome (run 4 of verify_general_start.py; its T1-T4 lines are identical to run 3 apart from timings)

```
T4' (registered after T4 was killed): same model, discrete z^2/N terms included
------------------------------------------------------------------------------------------
N=3000: t_low(M1)=-0.34333762 t_low(A's S_N=1, M2)=-0.34333762 rel u diff=0.0e+00
        t_up=-0.31098157  width=0.032356   predicted t_low=-0.346109 t_up=-0.314003 width=0.032106
        t_low-pred=+0.002771 (tol 0.0112, ok True)  t_up-pred=+0.003021 (tol 0.0112, ok True)
        |width-shifted pred|=0.000250  |width-noshift pred|=0.005597  shifted closer: True
        full-face maximiser at t_up: n=(1028,1028,944)  |n1-n2|=0  z(1/3-n3/N)=0.12423 (pred n3~949.9)
        z*log(M_full/P(N/3,N/3,N/3))=0.04530 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=5.3e-15  [0.2s]
N=30000: t_low(M1)=-0.37037464 t_low(A's S_N=1, M2)=-0.37037464 rel u diff=0.0e+00
        t_up=-0.34806909  width=0.022306   predicted t_low=-0.371064 t_up=-0.348481 width=0.022582
        t_low-pred=+0.000689 (tol 0.0035, ok True)  t_up-pred=+0.000412 (tol 0.0035, ok True)
        |width-shifted pred|=0.000276  |width-noshift pred|=0.004756  shifted closer: True
        full-face maximiser at t_up: n=(10206,10206,9588)  |n1-n2|=0  z(1/3-n3/N)=0.12078 (pred n3~9621.0)
        z*log(M_full/P(N/3,N/3,N/3))=0.04417 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=5.3e-15  [0.6s]
N=300000: t_low(M1)=-0.38521279 t_low(A's S_N=1, M2)=-0.38521279 rel u diff=0.0e+00
        t_up=-0.36380289  width=0.021410   predicted t_low=-0.385511 t_up=-0.363855 width=0.021656
        t_low-pred=+0.000298 (tol 0.0018, ok True)  t_up-pred=+0.000052 (tol 0.0018, ok True)
        |width-shifted pred|=0.000246  |width-noshift pred|=0.003873  shifted closer: True
        full-face maximiser at t_up: n=(101621,101622,96757)  |n1-n2|=1  z(1/3-n3/N)=0.11870 (pred n3~96964.3)
        z*log(M_full/P(N/3,N/3,N/3))=0.04363 (limit 1/24=0.04167)
        M2 confirms sign change at t_up +- 1e-9 rel: True  |M1-M2| log value at maximiser=0.0e+00  [1.0s]
total time 18.7s
```

Verdict: T4' survives. t_low - prediction = +0.00277, +0.00069, +0.00030 and t_up - prediction =
+0.00302, +0.00041, +0.00005 (tolerances 0.0112, 0.0035, 0.0018). The shifted width is closer
than the noshift width at all three N (0.00025 vs 0.0056, 0.00028 vs 0.0048, 0.00025 vs 0.0039).
Maximiser: |n1-n2| <= 1, z(1/3 - n3/N) = 0.1242, 0.1208, 0.1187 (in [0.09, 0.13]);
z log(M_full/P_bal) = 0.0453, 0.0442, 0.0436 (in [0.035, 0.050]). Post hoc: the remaining t_low
residual is about +0.05/z^2, the t_up residual smaller; neither is used anywhere.

## 2026-09-26 Repair pass after the read-only audit of B_tie.md (entries appended; nothing above is changed)

### Corrections to statements recorded above
- T1 verdict, sentence "which (c) proves exactly": wrong. T1(c) tests det Sigma = 2^{k-1}(prod alpha)^2/tau
  (Lemma K1). T1(e) tested a different identity, the Legendre identity det Hess I * det Sigma = 1
  (Sigma_alpha = (Hess I)^{-1}, C5 Prop 4(a)). At the time of the kill no exact test covered it at general
  alpha; it had been checked by hand at k = 2 (I'' = 1/(2f^3), Sigma = 2f^3, f = sqrt(alpha_1 alpha_2))
  and at the center (Prop MB). The kill of T1(e) stands. An exact test is registered below as T1(e').
- T4 prior-data note: the N = 1000002 cell is not blind (C's P6/P6' had measured N = 1e6). The value
  0.021710 registered in T4(ii) for that cell is the no-z^2/N formula that T4 killed; it must not be quoted as
  a confirmation anywhere. The blind confirmations of the second-order window ends are T4' (N = 3000, 30000,
  300000) only.
- Number in the notes (not in this ledger): the finite-N width coefficient W/2 + 1/24 was printed as
  0.0546960 in B_tie.md; the correct value is 0.0546957 (W = log(16/(9 sqrt 3)) = 0.0260580006,
  W/2 + 1/24 = 0.0546956670). No registered prediction used it.
- T4/T4' search method, stated for the record: for N >= 1002 the full-face maximum at each u was found by a
  1D step-halving search along n1 = ceil((N-n3)/2), n2 = floor((N-n3)/2), started at the predicted n3, and
  then a 5 x 7 neighbourhood check (n3 +- 2, n1 - n2 in -3..3) at the final u only. M2 re-evaluates the value
  at M1's maximiser; it does not search. Global maximality was checked only at N = 90 (DP, M3). So the
  t_up values at N >= 1002 rest on the assumption that the full-face maximum lies on (or next to) the line
  n1 = n2 and is unimodal along it. T4'' below adds a second global check at a new cell.

### 2026-09-26 T1(e') (exact Legendre identity; registered before any code for it runs)
Setting: K_k face, I(alpha) = k - A^2 (the constant is irrelevant), A = sum sqrt(alpha_i), coordinates
alpha' = (alpha_2..alpha_k), alpha_1 = 1 - sum alpha'. Points: alpha_i = x_i^2 with x a rational point of
the unit sphere with positive coordinates (inverse stereographic projection of t in Q_{>0}^{k-1}, |t| < 1),
so sqrt(alpha_i) = x_i is rational and Hess I is rational. Three points for each k = 2..6.
Method 1 (Hess I): closed form, dA/dalpha_j = 1/(2x_j) - 1/(2x_1),
d2A/dalpha_j dalpha_l = -delta_jl/(4x_j^3) - 1/(4x_1^3), Hess(A^2) = 2 grad A grad A^T + 2A Hess A,
Hess I = -Hess(A^2), exact Fractions.
Method 2 (Hess I): 80-digit Decimal central differences of I in alpha' with step 1e-25.
Sigma_alpha: Doob chain G_ij = x_j/x_i, Gamma = D Z + Z^T D from the fundamental matrix (exact Fractions,
same construction as T1(c)), Sigma = Gamma without row and column 1.
Predictions: (i) Hess I * Sigma = identity matrix of size k-1, exactly, at all 15 points;
(ii) methods 1 and 2 for Hess I agree entrywise to relative 1e-20; (iii) hence det Hess I * det Sigma = 1
exactly. Runtime estimate: under 5 seconds.
Kill: any of (i)-(iii) fails.

### 2026-09-26 T4'' (second global check of the full-face search; new cell N = 300; registered before any code for it runs)
K_3, mu = (1/2,1/2,0), N = 300 (never computed before). Same M1 code path as T4 for t_low and t_up (line
search along n1 = n2 plus the 5 x 7 neighbourhood). Then an exact-recursion float DP over all bins (M3,
forward over positions with state (n1, n2, last letter)) at u_- = u_up (1 - 1e-7) and u_+ = u_up (1 + 1e-7).
Predictions from the T4' equations (formula evaluation only, predict_general_start.py functions):
 N=300  t_low=-0.291539  t_up=-0.211297  width=0.080241  (noshift t_up=-0.202854), tol 0.2/z^2+3z/N = 0.0551
Predictions:
(i) t_low (M1) equals the root of Paper A's S_{(150,150)}(u) = 1 (M2) to 1e-10 relative in u;
(ii) |t_low - (-0.291539)| <= 0.0551 and |t_up - (-0.211297)| <= 0.0551;
(iii) DP total mass 1 to 1e-12; DP and M1 values at the M1 maximiser agree to 1e-12 relative;
(iv) global modes from the DP: at u_- exactly {(150,150,0)}; at u_+ exactly the M1 maximiser and, if
n1 != n2, its swap; and at both u_- and u_+ the DP's maximum over bins with three positive counts is
attained at the M1 maximiser (or its swap);
(v) the maximiser has |n1 - n2| <= 1 and z(1/3 - n3/N) in [0.10, 0.20] (pred n3 ~ 92.8).
Runtime estimate: M1 part under 1 s; each DP about 1.5 N^3 = 4e7 elementary updates, 30 to 90 s in pure
Python; two DPs, so under 4 minutes.
Kill: any of (i)-(v) fails.

### T1(e') and T4'' outcome (verify_B_tie_repair.py, run 1, verbatim)

```
==========================================================================================
T1(e')  exact Legendre identity: Hess_{alpha'} I * Sigma_alpha = identity (K_k)
------------------------------------------------------------------------------------------
   k=2 x=['24/25', '7/25']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 9.6e-32
   k=2 x=['77/85', '36/85']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 5.8e-31
   k=2 x=['56/65', '33/65']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 1.2e-30
   k=3 x=['1151/1299', '350/1299', '490/1299']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 2.7e-30
   k=3 x=['1151/1441', '576/1441', '648/1441']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 4.3e-30
   k=3 x=['2502/3427', '1617/3427', '1694/3427']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 1.7e-30
   k=4 x=['91747/115278', '29575/115278', '41405/115278', '15925/38426']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 2.9e-29
   k=4 x=['26471/38329', '14400/38329', '16200/38329', '17280/38329']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 5.0e-30
   k=4 x=['1297931/2129031', '311542/709677', '979132/2129031', '1007930/2129031']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 2.4e-30
   k=5 x=['2728879/3895921', '946400/3895921', '1324960/3895921', '1528800/3895921', '1656200/3895921']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 1.4e-29
   k=5 x=['23971/40829', '14400/40829', '16200/40829', '17280/40829', '18000/40829']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 4.7e-30
   k=5 x=['114371771/228324429', '31154200/76108143', '97913200/228324429', '100793000/228324429', '34269620/76108143']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 1.4e-30
   k=6 x=['902315319/1489237481', '341650400/1489237481', '478310560/1489237481', '551896800/1489237481', '597888200/1489237481', '629356000/1489237481']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 4.1e-30
   k=6 x=['1044979/2130221', '705600/2130221', '793800/2130221', '846720/2130221', '882000/2130221', '907200/2130221']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 8.2e-31
   k=6 x=['52106609959/129179679841', '49441715400/129179679841', '51796082800/129179679841', '53319497000/129179679841', '54385886940/129179679841', '55174088200/129179679841']
        Hess I * Sigma == I exactly: True   det Hess I * det Sigma == 1: True   Decimal FD vs exact Hess, worst rel: 8.0e-31
   (i) all 15 points identity: True   (ii) worst FD rel diff 2.9e-29 (<= 1e-20: True)   (iii) all det products 1: True
==========================================================================================
T4''  K_3, mu=(1/2,1/2,0), N=300: M1 line search checked globally by a DP over all bins
------------------------------------------------------------------------------------------
N=300: t_low(M1)=-0.27654591 t_low(A's S_N=1, M2)=-0.27654591 rel u diff=0.0e+00
        t_up=-0.19226282  width=0.084283   predicted t_low=-0.291539 t_up=-0.211297
        t_low-pred=+0.014993 (tol 0.0551, ok True)  t_up-pred=+0.019034 (tol 0.0551, ok True)
        M1 full-face maximiser at t_up: n=(104, 105, 91)  |n1-n2|=1  z(1/3-n3/N)=0.13923  [M1 part 0.1s]
   DP at u_- (t=-0.19226328): total mass 1.000000000000000; global modes [(150, 150, 0)]; full-face DP max at [(104, 105, 91), (105, 104, 91)]; |log DP - log M1| at M1 maximiser = 4.4e-15  [1.4s]
   DP at u_+ (t=-0.19226235): total mass 1.000000000000000; global modes [(104, 105, 91), (105, 104, 91)]; full-face DP max at [(104, 105, 91), (105, 104, 91)]; |log DP - log M1| at M1 maximiser = 4.5e-14  [1.4s]
   (iv) global-mode prediction holds: True
   total 2.8s
total time 2.9s
```

Verdicts (written after reading the output above).
- T1(e') survives. (i) Hess I * Sigma = identity exactly at all 15 rational points, k = 2..6; (ii) the
  80-digit finite differences agree with the exact Hessian to <= 2.9e-29 relative; (iii) all determinant
  products are exactly 1. The Legendre identity Sigma_alpha = (Hess I)^{-1} is now covered by an exact test
  at general alpha (it remains a standard fact, C5 Prop 4(a); the test is a check, not the proof).
- T4'' survives. (i) M1 = M2 root, 0 relative difference; (ii) t_low - pred = +0.0150, t_up - pred = +0.0190
  (tolerance 0.0551); (iii) mass 1, |log DP - log M1| <= 4.5e-14; (iv) the DP over all 45451 bins gives the
  single global mode (150,150,0) at u_- and the pair (104,105,91)/(105,104,91) at u_+, and at both u_- and
  u_+ the full-face DP maximum is that pair, which is the M1 line-search maximiser and its swap; (v)
  |n1 - n2| = 1 and z(1/3 - n3/N) = 0.139 (in [0.10, 0.20]). The DP took 1.4 s per call, far below the
  estimate.

### 2026-09-26 T4''' (global DP check at the T4 cell N = 1002; registered before any code for it runs)
Because the N = 300 DP took 1.4 s, a DP at a reported cell is affordable: estimate 1.4 s * (1002/300)^3,
about 55 s per call, two calls, under 3 minutes; memory kept down with array('d') rows.
Re-run the T4 M1 code path at N = 1002 (same function body as T4''), then the DP at u_up (1 -+ 1e-7).
Predictions: (i) t_up reproduces the T4 run-3 value -0.27171620 to 1e-8 and the M1 maximiser is
(345,345,312); (ii) DP total mass 1 to 1e-12 and |log DP - log M1| at the maximiser <= 1e-11; (iii) DP
global modes: exactly {(501,501,0)} at u_-, exactly {(345,345,312)} at u_+; at both, the DP's maximum over
bins with three positive counts is (345,345,312) only.
Kill: any of (i)-(iii) fails.

### T4''' outcome (verify_B_tie_repair.py, run 2; its T1(e') and T4'' lines are identical to run 1 apart from timings; T4''' lines verbatim)

```
T4'''  same global DP check at the T4 cell N = 1002 (t tolerances printed are T4's, already killed there)
------------------------------------------------------------------------------------------
N=1002: t_low(M1)=-0.31970797 t_low(A's S_N=1, M2)=-0.31970797 rel u diff=0.0e+00
        t_up=-0.27171620  width=0.047992   predicted t_low=-0.340235 t_up=-0.323179
        t_low-pred=+0.020527 (tol 0.0476, ok True)  t_up-pred=+0.051463 (tol 0.0476, ok False)
        M1 full-face maximiser at t_up: n=(345, 345, 312)  |n1-n2|=0  z(1/3-n3/N)=0.12453  [M1 part 0.1s]
   DP at u_- (t=-0.27171677): total mass 0.999999999999999; global modes [(501, 501, 0)]; full-face DP max at [(345, 345, 312)]; |log DP - log M1| at M1 maximiser = 1.4e-13  [77.8s]
   DP at u_+ (t=-0.27171563): total mass 1.000000000000000; global modes [(345, 345, 312)]; full-face DP max at [(345, 345, 312)]; |log DP - log M1| at M1 maximiser = 4.2e-14  [80.9s]
   (iv) global-mode prediction holds: True
   reproduces reference t_up -0.27171620: diff -1.5e-09 (<= 1e-8: True);  maximiser == (345, 345, 312): True
   total 158.8s
total time 162.5s
```

Verdict: T4''' survives. (i) t_up = -0.27171620 reproduced (difference -1.5e-9) with maximiser (345,345,312);
(ii) mass 1 to 1e-15, |log DP - log M1| <= 1.4e-13; (iii) over all 504,510 bins the DP gives the single global
mode (501,501,0) at u_- and (345,345,312) at u_+, and the full-face DP maximum is (345,345,312) at both. The
"ok False" in the printout is T4's old t_up tolerance at this cell, which was already killed; it is printed for
reference and is not a prediction of T4'''. Global maximality of the line-search maximiser is now checked by DP
at N = 90, 300 and 1002; for N >= 3000 it still rests on the line-search assumption (symmetry mu_1 = mu_2 plus
unimodality along n1 = n2), supported by these three cells. Runtime 163 s (estimate was under 3 minutes).
Correction to the verdict line just above: the number of bins at N = 1002 is C(1004,2) = 503,506, not 504,510.
