# Problem 131 Paper C, topic C3 ledger (linear observables; planar persistent walk, corner vs origin)

Predictions are appended before the computation that tests them; outcomes are appended verbatim below, never deleted.

## 2026-09-25 | Disclosure of computations already run before this entry

- Reproduction of planar_run.py's table (N = 40, 80, 160, 320; the six (r,s) pairs of program.md). These cells are reported in program.md, so they need no prediction. Output: code/out/C3_planar_run_orig_output.txt (original script) and code/out/C3_reproduce.txt (my engines). Every T*, tau_N and EW share agrees with program.md to the printed digits.
- Engine validation (code/C3_validate.py, out/C3_validate.txt): the origin probability at one non-crossing h per (N, r, s), including (r,s) = (1,0) and (0.3,1) at N = 40 and 80. This checks engine agreement only (brute force, Fourier, DP, three-level agree to about 1e-14). No crossing for a new cell was computed.
- N-free continuum functions Phi(T) (code/C3_continuum.py) and theory-only models (code/C3_model.py, C3_predict.py). These use the closed-form corner, the proved identity (zero-turn origin part) = 2 S_N(u) * corner, Paper A's S_N, and the N -> oo limit Phi. No finite-N planar origin probability at a new cell enters them.
- Calibration of model M3 against the reported cells N <= 320 (out/C3_model_calib.txt): M3 - exact T* = 3.9e-4, 2.6e-4, 1.4e-4, 6.5e-5 for (0.1,1) and 1.45e-2, 1.08e-2, 7.2e-3, 4.5e-3 for (1,1) at N = 40, 80, 160, 320. M3 - exact S_N(u*) = 2.6e-4, 1.6e-4, 8e-5, 4e-5 for (0.1,1) and 6.0e-3, 3.2e-3, 1.65e-3, 8.0e-4 for (1,1).

Definitions: T* = N h* where P(Y=0) = P(Y=(N,0)) (unique root, since the ratio is increasing in h); tau_N = T*/log N; EW share = S_N(u*) with u* = s h*/(1-(2r+s)h*), i.e. the fraction of the origin mass carried by east-west paths at the crossing.
Models: M3 solves 2 S_N(u) + Phi(T)/(N^2 corner) = 1 with the exact continuum Phi. M2 replaces Phi by (2(r+s)/pi)(T + c1), c1 = 1/(4r) - 1/(2(r+s)). M1 is the leading formula (2r+s) T = 2 log N - log log N + log(pi (2r+s)/(16(r+s))).
Exact computation plan: three-level exact representation (code/C3_core.py, origin_threelevel) for the root, with the Fourier inversion (K = N+1) evaluated at the root as a second method.

## 2026-09-25 | C3-P1: (r,s) = (0.1, 1.0), s/2r = 5, N = 640

- Rigorous (Theorem 3 bracket, from Paper A's Bessel bound plus my counting bound): s T* in [4.430075, 4.560856].
  Kill: exact s T* outside this interval (would mean a false theorem or a bug).
- M3 point: T* = 4.548293, tau_640 = 0.70391, S_N(u*) = 0.497809.
  Prediction: 0 <= M3 - exact T* <= 1.2e-4, so exact T* in [4.548173, 4.548293]; and 0 <= M3 - exact S_N(u*) <= 8e-5, so exact EW share in [0.497729, 0.497809].
  Kill: either quantity outside its band.
- Structural: the EW share keeps rising toward 1/2, i.e. S_640(u*) > 0.49683 (the N = 320 value). Kill: not larger.

## 2026-09-25 | C3-P2: (r,s) = (1.0, 1.0), s/2r = 0.5, N = 640

- M3 point: T* = 3.260498, tau = 0.50461, S_N(u*) = 0.117716. M2 point: T* = 3.261343. M1 (leading, no E-W correction): T* = 3.278229.
  Prediction: 0.001 <= M3 - exact T* <= 0.004, so exact T* in [3.256498, 3.259498] and tau_640 in [0.50445, 0.50492]; and 0.0001 <= M3 - exact S_N(u*) <= 0.0008, so exact EW share in [0.116916, 0.117616].
  Kill: either outside its band.
- Structural: the EW share keeps falling: S_640(u*) < 0.14216 (the N = 320 value), and 2 S_N(u*) is consistent with decay like N^{-(2r-s)/(2r+s)} = N^{-1/3} up to logs: the ratio S_640/S_320 lies in [0.75, 0.90]. Kill: outside.
- M1 accuracy: exact T* - M1 in [-0.030, -0.015] (the E-W correction log(1 - 2 S_N) is still -0.24 in beta T at this size). Kill: outside.

## 2026-09-25 | C3-P3: new pair (r,s) = (1.0, 0.0), pure turns, N = 40, 80, 160, 320, 640

Theory: rotate by 45 degrees. With s = 0 each switch flips exactly one of the two diagonal signs, so exactly
P(origin)/P(corner) = S_N(x)^2 - Delta_N(x), with x = r h/(1-2 r h) and Delta_N >= 0 (pairs of flip sets that share a position).
Consequence (rigorous): x* >= u_N (Paper A's root), i.e. T* >= T_A := N u_N/(r(1+2u_N)).
Heuristic: Delta_N/S_N^2 ~ delta_pred = (E|A|)^2/(N-1), with E|A| = d log S_N/d log x at u_N.

| N | T_A (rigorous lower bound) | delta_pred | delta-model T* [band: delta x 0.5 .. 1.5] | M3 T* |
|---|---|---|---|---|
| 40 | 2.538112 | 0.26203 | 2.643410 [2.586783, 2.711098] | 2.670334 |
| 80 | 3.175785 | 0.18371 | 3.253707 [3.212765, 3.299561] | 3.269632 |
| 160 | 3.827756 | 0.12362 | 3.882017 [3.853987, 3.912110] | 3.891526 |
| 320 | 4.483382 | 0.08038 | 4.519448 [4.501035, 4.538691] | 4.525128 |
| 640 | 5.138363 | 0.05082 | 5.161504 [5.149782, 5.173547] | 5.164860 |

- Kill (identity): exact T* < T_A at any N.
- Kill (delta-model): exact T* outside the band at N = 160, 320 or 640 (at N = 40, 80 the band is reported but not binding, since delta_pred is not small).
- M3: 0 <= M3 - exact T* <= 0.012 at N = 320 and 0 <= M3 - exact T* <= 0.008 at N = 640. Kill: outside.
- EW share is identically 0 here (no reversals); the whole origin mass is four-directional.

## 2026-09-25 | C3-P4: new pair (r,s) = (0.3, 1.0), s/2r = 1.667 (reversal-dominated, near the switch), N = 40 .. 640

Theorem 3's upper end still applies: s T* <= 4.547892 at N = 640 (its lower end is vacuous here because the crude eta exceeds 1). Error exponent (s-2r)/s = 0.4, so the four-direction share should decay slowly.

| N | M3 T* | M3 S_N(u*) | Thm3 upper bound on s T* |
|---|---|---|---|
| 40 | 2.052284 | 0.466157 | 2.187100 |
| 80 | 2.627564 | 0.466233 | 2.731184 |
| 160 | 3.234294 | 0.468520 | 3.315840 |
| 320 | 3.859887 | 0.472126 | 3.924714 |
| 640 | 4.496341 | 0.476257 | 4.547892 |

- Kill (rigorous): exact s T* above the Theorem 3 upper bound at any N.
- M3 accuracy: |M3 - exact T*| <= 0.01 at N = 40, 80; <= 0.004 at N = 160, 320; <= 0.002 at N = 640. |M3 - exact S_N(u*)| <= 0.004 at N = 40, 80; <= 0.0015 at N = 160, 320; <= 5e-4 at N = 640. Kill: any outside.
- Structural: S_N(u*) increases with N from N = 80 on (toward 1/2, but slowly). Kill: a decrease between consecutive sizes from 80 to 640.

## 2026-09-25 | C3-P5: the switch s = 2r, (r,s) = (0.5, 1.0), N = 640

Theory (Corollary 10(c) in C3.md, from Theorem 9 plus Paper A's Bessel bound): at s = 2r both faces cost 2 at tau* = 1/s, and the zero-turn share of the origin mass at the crossing tends to 2 sqrt2/(sqrt2 + sqrt5) = 0.774852, so the EW share S_N(u*) -> sqrt2/(sqrt2+sqrt5) = 0.387426. It does not tend to 0 or 1.
Calibration (reported cells): exact S_N(u*) = 0.40899, 0.39839, 0.39131, 0.38689 at N = 40..320; M3 - exact T* = 7.6e-3, 6.1e-3, 4.3e-3, 2.8e-3; M3 - exact S_N = 4.6e-3, 3.3e-3, 2.1e-3, 1.3e-3.
M3 at N = 640: T* = 4.297685, tau = 0.66513, S_N(u*) = 0.385075 (code/out/C3_predict_switch.txt).

- Prediction: 0.0005 <= M3 - exact T* <= 0.0022, so exact T* in [4.295485, 4.297185]; 0.0003 <= M3 - exact S_N(u*) <= 0.0010, so exact EW share in [0.384075, 0.384775].
  Kill: either outside its band.
- Structural: at N = 640 the EW share lies below its limit 0.387426 (so the approach is non-monotone: from above at small N, from below at large N, driven by the positive 1/T corrections c1 = 1/6 and the Bessel 1/(8z) term). Kill: S_640(u*) >= 0.387426.

### 2026-09-25 | Outcomes for C3-P1 .. C3-P4 (code/C3_run_new.py; three-level exact root, Fourier K=N+1 at the root)

Verbatim output (out/C3_run_new.txt):
```
(r,s)=(0.1,1.0) N=640: T*=4.5482653 sT*=4.5482653 tau_N=0.703906 EWshare=S_N(u*)=0.4977939 zero-turn=0.9955879 4dir=0.0044121 tail/corner=3.2e-63 |Fourier/corner-1|=2.5e-13 [62s,8s]
(r,s)=(1.0,1.0) N=640: T*=3.2577636 sT*=3.2577636 tau_N=0.504183 EWshare=S_N(u*)=0.1173326 zero-turn=0.2346652 4dir=0.7653348 tail/corner=1.8e-42 |Fourier/corner-1|=9.1e-14 [56s,5s]
(r,s)=(1.0,0.0) N=40: T*=2.6427593 sT*=0.0000000 tau_N=0.716412 EWshare=S_N(u*)=0.0000000 zero-turn=0.0000000 4dir=1.0000000 tail/corner=0.0e+00 |Fourier/corner-1|=2.2e-16 [11s,0s]
(r,s)=(1.0,0.0) N=80: T*=3.2524385 sT*=0.0000000 tau_N=0.742222 EWshare=S_N(u*)=0.0000000 zero-turn=0.0000000 4dir=1.0000000 tail/corner=0.0e+00 |Fourier/corner-1|=1.9e-14 [0s,0s]
(r,s)=(1.0,0.0) N=160: T*=3.8810744 sT*=0.0000000 tau_N=0.764718 EWshare=S_N(u*)=0.0000000 zero-turn=0.0000000 4dir=1.0000000 tail/corner=3.8e-58 |Fourier/corner-1|=1.0e-14 [0s,0s]
(r,s)=(1.0,0.0) N=320: T*=4.5189207 sT*=0.0000000 tau_N=0.783403 EWshare=S_N(u*)=0.0000000 zero-turn=0.0000000 4dir=1.0000000 tail/corner=2.4e-47 |Fourier/corner-1|=7.8e-14 [1s,1s]
(r,s)=(1.0,0.0) N=640: T*=5.1612511 sT*=0.0000000 tau_N=0.798774 EWshare=S_N(u*)=0.0000000 zero-turn=0.0000000 4dir=1.0000000 tail/corner=1.7e-40 |Fourier/corner-1|=7.4e-14 [2s,6s]
(r,s)=(0.3,1.0) N=40: T*=2.0493720 sT*=2.0493720 tau_N=0.555554 EWshare=S_N(u*)=0.4642576 zero-turn=0.9285153 4dir=0.0714847 tail/corner=0.0e+00 |Fourier/corner-1|=2.0e-15 [16s,0s]
(r,s)=(0.3,1.0) N=80: T*=2.6254217 sT*=2.6254217 tau_N=0.599134 EWshare=S_N(u*)=0.4649484 zero-turn=0.9298968 4dir=0.0701032 tail/corner=0.0e+00 |Fourier/corner-1|=5.0e-14 [5s,0s]
(r,s)=(0.3,1.0) N=160: T*=3.2329623 sT*=3.2329623 tau_N=0.637015 EWshare=S_N(u*)=0.4677634 zero-turn=0.9355268 4dir=0.0644732 tail/corner=5.0e-73 |Fourier/corner-1|=4.1e-14 [14s,0s]
(r,s)=(0.3,1.0) N=320: T*=3.8591484 sT*=3.8591484 tau_N=0.669025 EWshare=S_N(u*)=0.4717193 zero-turn=0.9434387 4dir=0.0565613 tail/corner=4.4e-61 |Fourier/corner-1|=3.3e-14 [24s,1s]
(r,s)=(0.3,1.0) N=640: T*=4.4959627 sT*=4.4959627 tau_N=0.695811 EWshare=S_N(u*)=0.4760532 zero-turn=0.9521065 4dir=0.0478935 tail/corner=2.1e-53 |Fourier/corner-1|=3.2e-13 [48s,7s]
```

Verdicts:
- C3-P1 (0.1,1), N = 640. Theorem 3 bracket: s T* = 4.5482653 in [4.430075, 4.560856], SURVIVES. M3 - exact T* = 4.548293 - 4.5482653 = 2.8e-5, in [0, 1.2e-4], SURVIVES. M3 - exact EW share = 0.497809 - 0.4977939 = 1.5e-5, in [0, 8e-5], SURVIVES. Structural: 0.4977939 > 0.49683, SURVIVES.
- C3-P2 (1,1), N = 640. M3 - exact T* = 3.260498 - 3.2577636 = 2.73e-3, in [0.001, 0.004], SURVIVES (exact T* = 3.2577636 in [3.256498, 3.259498]).
  tau band as written, [0.50445, 0.50492]: exact tau_640 = 0.504183 lies OUTSIDE, so this sub-prediction is KILLED as written. Cause: an arithmetic slip at registration. The T band [3.256498, 3.259498] divided by log 640 = 6.461468 is [0.503987, 0.504451], and the exact value lies inside that. I keep the kill on the record, because the band was written before the computation.
  EW share: M3 - exact = 0.117716 - 0.1173326 = 3.8e-4, in [1e-4, 8e-4], SURVIVES. Structural: S_640 = 0.1173326 < 0.14216 and S_640/S_320 = 0.8254 in [0.75, 0.90], SURVIVES. M1 accuracy: exact - M1 = 3.2577636 - 3.278229 = -0.0205, in [-0.030, -0.015], SURVIVES.
- C3-P3 (1,0). Identity bound T* >= T_A: 2.6428 >= 2.5381, 3.2524 >= 3.1758, 3.8811 >= 3.8278, 4.5189 >= 4.4834, 5.1613 >= 5.1384, SURVIVES at all N.
  delta-model (exact - model): -6.5e-4, -1.27e-3, -9.4e-4, -5.3e-4, -2.5e-4 at N = 40..640; inside the binding bands at N = 160, 320, 640, SURVIVES. The model is much sharper than its band.
  M3 - exact: 6.2e-3 at N = 320 (band [0, 0.012]) and 3.6e-3 at N = 640 (band [0, 0.008]), SURVIVES.
- C3-P4 (0.3,1). Theorem 3 upper bound holds at every N (exact s T* = 2.0494, 2.6254, 3.2330, 3.8591, 4.4960 against bounds 2.1871, 2.7312, 3.3158, 3.9247, 4.5479), SURVIVES.
  M3 - exact T* = 2.9e-3, 2.1e-3, 1.3e-3, 7.4e-4, 3.8e-4 (bands 0.01, 0.01, 0.004, 0.004, 0.002), SURVIVES. M3 - exact EW share = 1.9e-3, 1.3e-3, 7.6e-4, 4.1e-4, 2.0e-4 (bands 0.004, 0.004, 0.0015, 0.0015, 5e-4), SURVIVES. Structural: the EW share increases 0.46426, 0.46495, 0.46776, 0.47172, 0.47605, SURVIVES.

### 2026-09-25 | Outcome for C3-P5 (code/C3_run_new.py 0.5,1.0,640)

Verbatim output (out/C3_run_switch.txt):
```
(r,s)=(0.5,1.0) N=640: T*=4.2960095 sT*=4.2960095 tau_N=0.664866 EWshare=S_N(u*)=0.3843369 zero-turn=0.7686739 4dir=0.2313261 tail/corner=4.6e-47 |Fourier/corner-1|=2.3e-13 [56s,6s]
```
Verdicts: M3 - exact T* = 4.297685 - 4.2960095 = 1.68e-3, in [0.0005, 0.0022], SURVIVES. M3 - exact EW share = 0.385075 - 0.3843369 = 7.4e-4, in [3e-4, 1e-3], SURVIVES. Structural: S_640(u*) = 0.3843369 < 0.387426, SURVIVES (the share passed below its limit between N = 160 and 640 and keeps falling at this size; the theory says it returns to 0.387426 as N grows).

Third-method spot check (code/C3_dp640.py, direction-x-y DP at N = 640, evaluated at the rounded root T = 3.2577636 for (1,1)): P(origin)/corner - 1 = 1.24e-07, consistent with rounding the root to 7 decimals.

## 2026-09-25 | C3-P6: asymptotic regime, N = 1280, 2560, 5120, 10240 for (0.1,1), (1,1), (0.5,1), (1,0)

Theory-only inputs: code/out/C3_predict_big.txt (M3), bands computed by code/C3_bands_big.py. Band rule: exact = M3 - D with D in [0.35^k, 0.75^k] * D_640, k = log2(N/640), where D_640 is the observed M3 - exact at N = 640 (T: 2.77e-5, 2.734e-3, 1.676e-3, 3.609e-3; EW share: 1.51e-5, 3.83e-4, 7.38e-4, 0). This says the M3 error keeps the sign seen at N <= 640 and shrinks roughly like T^2/N.

| (r,s) | N | M3 T* | exact T* band | tau band | M3 EW share | exact EW share band |
|---|---|---|---|---|---|---|
| (0.1,1.0) | 1280 | 5.1808884 | [5.1808676, 5.1808787] | [0.724129, 0.724131] | 0.4985204 | [0.4985091, 0.4985151] |
| (0.1,1.0) | 2560 | 5.8188505 | [5.8188349, 5.8188471] | [0.741464, 0.741466] | 0.4990264 | [0.4990179, 0.4990246] |
| (0.1,1.0) | 5120 | 6.4611815 | [6.4611698, 6.4611803] | [0.756497, 0.756498] | 0.4993724 | [0.4993660, 0.4993718] |
| (0.1,1.0) | 10240 | 7.1072718 | [7.1072630, 7.1072714] | [0.769679, 0.769680] | 0.4996020 | [0.4995972, 0.4996018] |
| (1.0,1.0) | 1280 | 3.7038250 | [3.7017742, 3.7028680] | [0.517397, 0.517550] | 0.0966615 | [0.0963739, 0.0965273] |
| (1.0,1.0) | 2560 | 4.1470748 | [4.1455367, 4.1467398] | [0.528244, 0.528398] | 0.0791340 | [0.0789183, 0.0790870] |
| (1.0,1.0) | 5120 | 4.5900393 | [4.5888857, 4.5899221] | [0.537283, 0.537404] | 0.0645896 | [0.0644279, 0.0645732] |
| (1.0,1.0) | 10240 | 5.0328327 | [5.0319675, 5.0327917] | [0.544936, 0.545025] | 0.0525675 | [0.0524462, 0.0525617] |
| (0.5,1.0) | 1280 | 4.9290889 | [4.9278323, 4.9285025] | [0.688763, 0.688856] | 0.3834348 | [0.3828812, 0.3831765] |
| (0.5,1.0) | 2560 | 5.5667589 | [5.5658164, 5.5665537] | [0.709223, 0.709317] | 0.3826963 | [0.3822811, 0.3826059] |
| (0.5,1.0) | 5120 | 6.2091516 | [6.2084447, 6.2090798] | [0.726907, 0.726981] | 0.3824885 | [0.3821771, 0.3824569] |
| (0.5,1.0) | 10240 | 6.8553938 | [6.8548637, 6.8553687] | [0.742346, 0.742401] | 0.3825721 | [0.3823386, 0.3825610] |
| (1.0,0.0) | 1280 | 5.8082670 | [5.8055603, 5.8070039] | [0.811443, 0.811644] | 0 | 0 |
| (1.0,0.0) | 2560 | 6.4544345 | [6.4524045, 6.4539924] | [0.822197, 0.822399] | 0 | 0 |
| (1.0,0.0) | 5120 | 7.1030875 | [7.1015650, 7.1029328] | [0.831476, 0.831637] | 0 | 0 |
| (1.0,0.0) | 10240 | 7.7541538 | [7.7530119, 7.7540996] | [0.839611, 0.839728] | 0 | 0 |

- Kill (bands): any exact T*, tau or EW share outside its band. I count each cell and quantity separately.
- Rigorous (Theorem 3), (0.1,1): s T* in [5.103321, 5.188306], [5.768505, 5.823216], [6.428814, 6.463742], [7.086634, 7.108770] at N = 1280, 2560, 5120, 10240. Kill: outside (a false theorem or a bug).
- Switch (0.5,1), sharper structural claim: the exact EW share has an interior minimum and turns back toward 0.387426. Precisely, S_10240(u*) > S_5120(u*), and all four values lie in [0.3815, 0.3875]. Kill: otherwise.
- Corollary 10 residual. Define rho_N = -(N-1) log(1-(2r+s)h*) + log T* - 2 log N - log(pi/(8(r+s))) - log(1 - 2 S_N(u*)). Edgeworth predicts rho_N = -c1/T* + O(T*^-2) + O(T*^2/N), with c1 = 1/(4r) - 1/(2(r+s)).
  (1,1): c1 = 0, prediction |rho_N| <= 0.02 at N = 5120 and 10240.
  (1,0): c1 = -1/4, prediction rho_N in [0.02, 0.05] at N = 5120 and 10240, and rho_N * T* in [0.15, 0.40] at N = 10240.
  Kill: outside.

Addendum (DP third method, all three N = 640 spot checks, out/C3_dp640.txt), P(origin)/corner - 1 at the rounded three-level roots:
```
(r,s)=(1.0,1.0) N=640 T=3.2577636: DP P(origin)/corner - 1 = 1.24e-07  [503s]
(r,s)=(0.1,1.0) N=640 T=4.5482653: DP P(origin)/corner - 1 = 5.33e-08  [505s]
(r,s)=(1.0,0.0) N=640 T=5.1612511: DP P(origin)/corner - 1 = 4.90e-08  [504s]
```

### 2026-09-25 | Outcomes for C3-P6 (code/C3_run_big.py for the N = 1280 cells and (0.1,1) at 2560; code/C3_run_pair.py for the rest; Fourier K = N+1 at the root for N <= 5120)

Note on numbering: "Theorem 3" in the entries above is Theorem 8 in C3.md (the notes were renumbered after these entries were written).

Verbatim outputs:
```
(r,s)=(0.1,1.0) N=1280: T*=5.18087744 sT*=5.18087744 tau_N=0.7241308 EWshare=0.49851428 4dir/corner=0.0029714 rho_N=0.411809 rho*T=2.13353 tail/corner=2.1e-46 |Fourier/corner-1|=1.1e-12 [65s,25s]
(r,s)=(1.0,1.0) N=1280: T*=3.70221925 sT*=3.70221925 tau_N=0.5174589 EWshare=0.09648150 4dir/corner=0.8070370 rho_N=-0.011644 rho*T=-0.04311 tail/corner=2.3e-28 |Fourier/corner-1|=8.0e-13 [71s,26s]
(r,s)=(0.5,1.0) N=1280: T*=4.92810714 sT*=4.92810714 tau_N=0.6888011 EWshare=0.38301378 4dir/corner=0.2339724 rho_N=-0.034920 rho*T=-0.17209 tail/corner=4.4e-32 |Fourier/corner-1|=1.0e-12 [57s,22s]
(r,s)=(1.0,0.0) N=1280: T*=5.80620711 sT*=0.00000000 tau_N=0.8115331 EWshare=0.00000000 4dir/corner=1.0000000 rho_N=0.040705 rho*T=0.23634 tail/corner=5.6e-27 |Fourier/corner-1|=8.2e-13 [3s,27s]
(r,s)=(0.1,1.0) N=2560: T*=5.81884636 sT*=5.81884636 tau_N=0.7414657 EWshare=0.49902412 4dir/corner=0.0019518 rho_N=0.324045 rho*T=1.88557 tail/corner=1.9e-42 |Fourier/corner-1|=1.1e-12 [106s,106s]
(r,s)=(0.1,1.0) N=5120: T*=6.46117995 sT*=6.46117995 tau_N=0.7564979 EWshare=0.49937155 4dir/corner=0.0012569 rho_N=0.250898 rho*T=1.62110 tail/corner=5.1e-39 |Fourier/corner-1|=1.5e-12 [227s,451s]
(r,s)=(0.1,1.0) N=10240: T*=7.10727127 sT*=7.10727127 tau_N=0.7696803 EWshare=0.49960168 4dir/corner=0.0007966 rho_N=0.189569 rho*T=1.34732 tail/corner=5.5e-36 |Fourier/corner-1|=nan [279s,0s]
(r,s)=(1.0,1.0) N=2560: T*=4.14615113 sT*=4.14615113 tau_N=0.5283227 EWshare=0.07905091 4dir/corner=0.8418982 rho_N=-0.009491 rho*T=-0.03935 tail/corner=1.6e-24 |Fourier/corner-1|=2.1e-13 [121s,106s]
(r,s)=(1.0,1.0) N=5120: T*=4.58951666 sT*=4.58951666 tau_N=0.5373569 EWshare=0.06455176 4dir/corner=0.8708965 rho_N=-0.007550 rho*T=-0.03465 tail/corner=3.1e-21 |Fourier/corner-1|=1.2e-12 [215s,383s]
(r,s)=(1.0,1.0) N=10240: T*=5.03254083 sT*=5.03254083 tau_N=0.5449978 EWshare=0.05255050 4dir/corner=0.8948990 rho_N=-0.005998 rho*T=-0.03018 tail/corner=2.6e-18 |Fourier/corner-1|=nan [251s,0s]
(r,s)=(0.5,1.0) N=2560: T*=5.56619750 sT*=5.56619750 tau_N=0.7092719 EWshare=0.38245982 4dir/corner=0.2350804 rho_N=-0.038496 rho*T=-0.21428 tail/corner=5.6e-28 |Fourier/corner-1|=6.5e-13 [106s,105s]
(r,s)=(0.5,1.0) N=5120: T*=6.20883595 sT*=6.20883595 tau_N=0.7269525 EWshare=0.38235717 4dir/corner=0.2352857 rho_N=-0.038388 rho*T=-0.23834 tail/corner=1.9e-24 |Fourier/corner-1|=2.0e-12 [216s,385s]
(r,s)=(0.5,1.0) N=10240: T*=6.85521855 sT*=6.85521855 tau_N=0.7423843 EWshare=0.38249980 4dir/corner=0.2350004 rho_N=-0.036475 rho*T=-0.25004 tail/corner=2.7e-21 |Fourier/corner-1|=nan [253s,0s]
(r,s)=(1.0,0.0) N=2560: T*=6.45327647 sT*=0.00000000 tau_N=0.8223078 EWshare=0.00000000 4dir/corner=1.0000000 rho_N=0.037918 rho*T=0.24469 tail/corner=2.2e-23 |Fourier/corner-1|=9.9e-14 [9s,119s]
(r,s)=(1.0,0.0) N=5120: T*=7.10244442 sT*=0.00000000 tau_N=0.8315794 EWshare=0.00000000 4dir/corner=1.0000000 rho_N=0.035183 rho*T=0.24989 tail/corner=2.9e-20 |Fourier/corner-1|=9.7e-13 [11s,463s]
(r,s)=(1.0,0.0) N=10240: T*=7.75380015 sT*=0.00000000 tau_N=0.8396959 EWshare=0.00000000 4dir/corner=1.0000000 rho_N=0.032620 rho*T=0.25293 tail/corner=1.8e-17 |Fourier/corner-1|=nan [23s,0s]
```
Verdicts (code/C3_verdict_big.py, same band code as at registration):
```
(0.1,1.0) N=1280: T*=5.18087744 in [5.1808676,5.1808787]: SURVIVES; tau=0.7241308 in [0.724129,0.724131]: SURVIVES; EW=0.49851428 in [0.4985091,0.4985151]: SURVIVES; Thm3 sT* in [5.103321,5.188306]: SURVIVES; M3-exact T=1.10e-05, rho_N=0.41181, rho*T=2.1335, |Fourier/corner-1|=1.1e-12
(0.1,1.0) N=2560: T*=5.81884636 in [5.8188349,5.8188471]: SURVIVES; tau=0.7414657 in [0.741464,0.741466]: SURVIVES; EW=0.49902412 in [0.4990179,0.4990246]: SURVIVES; Thm3 sT* in [5.768505,5.823216]: SURVIVES; M3-exact T=4.14e-06, rho_N=0.32405, rho*T=1.8856, |Fourier/corner-1|=1.1e-12
(0.1,1.0) N=5120: T*=6.46117995 in [6.4611698,6.4611803]: SURVIVES; tau=0.7564979 in [0.756497,0.756498]: SURVIVES; EW=0.49937155 in [0.4993660,0.4993718]: SURVIVES; Thm3 sT* in [6.428814,6.463742]: SURVIVES; M3-exact T=1.55e-06, rho_N=0.25090, rho*T=1.6211, |Fourier/corner-1|=1.5e-12
(0.1,1.0) N=10240: T*=7.10727127 in [7.1072630,7.1072714]: SURVIVES; tau=0.7696803 in [0.769679,0.769680]: KILLED; EW=0.49960168 in [0.4995972,0.4996018]: SURVIVES; Thm3 sT* in [7.086634,7.10877]: SURVIVES; M3-exact T=5.30e-07, rho_N=0.18957, rho*T=1.3473, |Fourier/corner-1|=nan
(0.5,1.0) N=1280: T*=4.92810714 in [4.9278323,4.9285025]: SURVIVES; tau=0.6888011 in [0.688763,0.688856]: SURVIVES; EW=0.38301378 in [0.3828812,0.3831765]: SURVIVES; M3-exact T=9.82e-04, rho_N=-0.03492, rho*T=-0.1721, |Fourier/corner-1|=1.0e-12
(0.5,1.0) N=2560: T*=5.56619750 in [5.5658164,5.5665537]: SURVIVES; tau=0.7092719 in [0.709223,0.709317]: SURVIVES; EW=0.38245982 in [0.3822811,0.3826059]: SURVIVES; M3-exact T=5.61e-04, rho_N=-0.03850, rho*T=-0.2143, |Fourier/corner-1|=6.5e-13
(0.5,1.0) N=5120: T*=6.20883595 in [6.2084447,6.2090798]: SURVIVES; tau=0.7269525 in [0.726907,0.726981]: SURVIVES; EW=0.38235717 in [0.3821771,0.3824569]: SURVIVES; M3-exact T=3.16e-04, rho_N=-0.03839, rho*T=-0.2383, |Fourier/corner-1|=2.0e-12
(0.5,1.0) N=10240: T*=6.85521855 in [6.8548637,6.8553687]: SURVIVES; tau=0.7423843 in [0.742346,0.742401]: SURVIVES; EW=0.38249980 in [0.3823386,0.3825610]: SURVIVES; M3-exact T=1.75e-04, rho_N=-0.03648, rho*T=-0.2500, |Fourier/corner-1|=nan
(1.0,0.0) N=1280: T*=5.80620711 in [5.8055603,5.8070039]: SURVIVES; tau=0.8115331 in [0.811443,0.811644]: SURVIVES; M3-exact T=2.06e-03, rho_N=0.04070, rho*T=0.2363, |Fourier/corner-1|=8.2e-13
(1.0,0.0) N=2560: T*=6.45327647 in [6.4524045,6.4539924]: SURVIVES; tau=0.8223078 in [0.822197,0.822399]: SURVIVES; M3-exact T=1.16e-03, rho_N=0.03792, rho*T=0.2447, |Fourier/corner-1|=9.9e-14
(1.0,0.0) N=5120: T*=7.10244442 in [7.1015650,7.1029328]: SURVIVES; tau=0.8315794 in [0.831476,0.831637]: SURVIVES; M3-exact T=6.43e-04, rho_N=0.03518, rho*T=0.2499, |Fourier/corner-1|=9.7e-13
(1.0,0.0) N=10240: T*=7.75380015 in [7.7530119,7.7540996]: SURVIVES; tau=0.8396959 in [0.839611,0.839728]: SURVIVES; M3-exact T=3.54e-04, rho_N=0.03262, rho*T=0.2529, |Fourier/corner-1|=nan
(1.0,1.0) N=1280: T*=3.70221925 in [3.7017742,3.7028680]: SURVIVES; tau=0.5174589 in [0.517397,0.517550]: SURVIVES; EW=0.09648150 in [0.0963739,0.0965273]: SURVIVES; M3-exact T=1.61e-03, rho_N=-0.01164, rho*T=-0.0431, |Fourier/corner-1|=8.0e-13
(1.0,1.0) N=2560: T*=4.14615113 in [4.1455367,4.1467398]: SURVIVES; tau=0.5283227 in [0.528244,0.528398]: SURVIVES; EW=0.07905091 in [0.0789183,0.0790870]: SURVIVES; M3-exact T=9.24e-04, rho_N=-0.00949, rho*T=-0.0394, |Fourier/corner-1|=2.1e-13
(1.0,1.0) N=5120: T*=4.58951666 in [4.5888857,4.5899221]: SURVIVES; tau=0.5373569 in [0.537283,0.537404]: SURVIVES; EW=0.06455176 in [0.0644279,0.0645732]: SURVIVES; M3-exact T=5.23e-04, rho_N=-0.00755, rho*T=-0.0347, |Fourier/corner-1|=1.2e-12
(1.0,1.0) N=10240: T*=5.03254083 in [5.0319675,5.0327917]: SURVIVES; tau=0.5449978 in [0.544936,0.545025]: SURVIVES; EW=0.05255050 in [0.0524462,0.0525617]: SURVIVES; M3-exact T=2.92e-04, rho_N=-0.00600, rho*T=-0.0302, |Fourier/corner-1|=nan
```
Extra verdicts (code/C3_p6_extra.py):
```
switch EW shares: {1280: 0.38301378, 2560: 0.38245982, 5120: 0.38235717, 10240: 0.3824998}
switch structural (S_10240 > S_5120, all in [0.3815,0.3875]): SURVIVES
(1,1) N=5120: rho_N=-0.007550, |rho|<=0.02: SURVIVES
(1,0) N=5120: rho_N=0.035183 in [0.02,0.05]: SURVIVES 
(1,1) N=10240: rho_N=-0.005998, |rho|<=0.02: SURVIVES
(1,0) N=10240: rho_N=0.032620 in [0.02,0.05]: SURVIVES ; rho*T=0.25293 in [0.15,0.40]: SURVIVES
```

Summary of C3-P6: 16 cells, 58 band checks, 4 Theorem-3 brackets, 1 switch claim, 5 residual claims.
- All T* bands, all EW-share bands, all Theorem 3 (= Theorem 8 in C3.md) brackets, the switch claim and the residual claims SURVIVE.
- One tau band is KILLED as written: (0.1,1) at N = 10240. The registered band is [0.769679, 0.769680], rounded to 6 decimals, and the exact tau = 7.10727127/log(10240) = 0.7696803 lies 3e-7 above its upper end. The T* band from which it was derived survives (7.10727127 <= 7.1072714), and unrounded (7.1072714/log 10240 = 0.76968027...) the tau band would also survive. So this is a registration rounding artifact, not a failure of the prediction. I keep the kill on the record as written.
- Switch: the exact EW share at (0.5,1) went 0.383014, 0.382460, 0.382357, 0.382500 at N = 1280..10240. It turned back up between 5120 and 10240, as predicted, toward sqrt2/(sqrt2+sqrt5) = 0.387426.
- Residual: rho_N * T* for (1,0) = 0.2499, 0.2529 at N = 5120, 10240, against Edgeworth's -c1 = 0.25.
- Correction to the first summary line above: the number of band checks is 44 (16 T*, 16 tau, 12 EW share), not 58.

## 2026-09-25 | Revision round after two verifier reports: label map, disclosures, and new pre-registered entries C3-P7, C3-P8

Label map (the notes were renumbered after the early entries): "Theorem 3" in C3-P1, P4, P6 is Theorem 8 of C3.md; "Corollary 10(c)" in C3-P5 is Corollary 10(b) of C3.md. Nothing above is edited.

Disclosure (re-analysis of cells already on record; no new crossing is computed): code/C3_fix_uniform.py recomputes, from the exact T* and EW shares recorded in C3-P1..P6, the Cor 10 uniform-form quantity D_N = beta T* - 2N(1-p_N) - l, l = log(1 - 2 S_N(u*)), and compares it with the third-order prediction with and without the term -l/(2L) that the rigor verifier found missing from Conjecture 11's display. It also evaluates the closed-form continuum function -T log(pi Phi_0(T)/(2T)) for (1,0) at the recorded T*, and the ratio numbers in the remark after Theorem 8. No prediction is attached to these; they are bookkeeping.

### C3-P7 (s = 0; new rigorous bounds from the revised Proposition 12). Registered before the runs.

Revised Prop 12 claims, for s = 0, x = rh/(1-2rh), q = rh, B_N(x) = 4x^2 + 16x^3(1+x)^(N-1) + 16(N-1)x^4(1+x)^(2(N-1)):
  4x^2 <= Delta_N(x) = S_N(x)^2 - o_N/c_N <= B_N(x)  for every even N >= 2 and x > 0.
- C3-P7a (exact rationals, new cells): even N = 2, 4, ..., 30 and x in {1/20, 1/7, 2/5, 1}. o_N/c_N from an exact DP in the 45-degree basis (pairs of +- words with disjoint flip sets), cross-checked against an exact (direction, x, y) DP of the planar walk for N <= 12; S_N(x) from an exact binary-word DP. Kill: any violation of either inequality, or any mismatch between the two DPs.
- C3-P7b (floats, new cells): r = 1, s = 0, T in {2, 5, 8}, N in {40, 160, 640, 2560}; N^2 o_N from the three-level engine (truncation tail reported), cross-checked by Fourier (K = N+1) for N <= 640. E_N := N^2 c_N (Delta_N - 4x^2).
  (i) rigorous: 0 <= E_N <= (4/N)[(Nx)^3 (1-q)^(N-1) + (Nx)^4 ((1-q)^2/(1-2q))^(N-1)]. Kill: violation.
  (ii) heuristic: err_N := N^2 o_N - Phi_0(T), Phi_0(T) = T^2 e^(-2T)[(I0(T)+I1(T))^2 - 1]; err_N > 0 at N >= 160 for all three T, and err_{4N}/err_N in [0.18, 0.32] for N = 160 -> 640 and 640 -> 2560 (O(1/N) convergence). Kill: outside.
- C3-P7c (check of a proved inequality on the (1,0) crossings already on record, N = 40 .. 10240): u_N <= x* <= u_N sqrt(1 + B_N(x*)), x* = h*/(1 - 2h*). Kill: violation.

### C3-P8 (new pair (r,s) = (0.55, 1.0), s/2r = 0.909, turn-dominated just below the switch; N = 640, 1280, 2560). Registered before the runs.

Purpose: a new-cell test of the corrected third-order form (Conjecture 11 with the -l/(2L) term). Here 2 S_N(u*) decays only like N^(-0.048), so l = log(1 - 2S_N(u*)) stays near -1.3 and the -l/(2L) term (about +0.1) is not negligible.
Constants: beta = 2.1, log(beta/(2(r+s))) = log(2.1/3.1) = -0.389465, gamma0 = (2r+s)(s-r)/(4r(r+s)) = 0.277126, c1 = gamma0/beta = 0.131965.
  pred_with(N)    = log(beta/(2(r+s))) + [ -log(beta/(2(r+s)))/2 - gamma0/2 - 1/4 - l/2 ] / L
  pred_without(N) = pred_with(N) + l/(2L)   (the display of C3.md before this revision)
  D_N = beta T* - 2N(1-p_N) - l, with p_N Paper A's crossing and l evaluated at the exact crossing.
Predictions (crude model: leading crossing equation with the (A1) Bessel form of 2S_N; it overestimates S by about 0.003 at the switch):
- T*_640 in [4.18, 4.28]; S_640(u*) in [0.32, 0.38]. Kill: outside.
- S_1280/S_640 and S_2560/S_1280 in [0.94, 0.995] (slow decay, N^(-0.048) up to logs). Kill: outside.
- R_N := D_N - pred_with in [-0.03, +0.04] at N = 640 and in [-0.025, +0.015] at N = 1280 and 2560. Kill: outside.
- |D_N - pred_without| >= 2 |R_N| at each N. Kill: otherwise.
- Theorem 9 ratio N^2 o4 / (2(r+s) T*/pi) in [1.00, 1.06] at each N. Kill: outside.
Method: three-level exact engine (code/C3_run_pair.py, MMAX = 70, truncation tail reported), Fourier K = N+1 at the root for N <= 1280.


## 2026-09-26 | Outcomes for C3-P7 and C3-P8 (recorded from the output files of the interrupted first repair; nothing rerun)

Provenance: the entries C3-P7 and C3-P8 above were written at 00:26 (ledger mtime at that point). code/C3_fix_p7.py was then run with parts a and c (output out/C3_fix_p7ac.txt, 00:28:02), and code/C3_run_pair.py was run for (0.55,1) at N = 640 (output out/C3_fix_p8_run.txt, 00:28:07). The session was then interrupted. This audit stage runs no new computations, so C3-P7b and the N = 1280, 2560 part of C3-P8 are NOT RUN and stay open.

### C3-P7a and C3-P7c: verbatim output (out/C3_fix_p7ac.txt)
```
=== C3-P7a: exact rationals
  45-degree DP vs (direction,x,y) DP, even N <= 12, 4 values of x: mismatches = 0
  N= 2 x=1/20: Delta=1.000000e-02  4x^2=1.000000e-02  B_N=1.221025e-02  (Delta-4x^2)/(B_N-4x^2)=0.000e+00
  N=10 x=1/20: Delta=1.045741e-02  4x^2=1.000000e-02  B_N=1.526861e-02  (Delta-4x^2)/(B_N-4x^2)=8.682e-02
  N=30 x=1/20: Delta=1.588920e-02  4x^2=1.000000e-02  B_N=6.736573e-02  (Delta-4x^2)/(B_N-4x^2)=1.027e-01
  N= 2 x=1/7 : Delta=8.163265e-02  4x^2=8.163265e-02  B_N=1.436476e-01  (Delta-4x^2)/(B_N-4x^2)=0.000e+00
  N=10 x=1/7 : Delta=1.455777e-01  4x^2=8.163265e-02  B_N=9.002595e-01  (Delta-4x^2)/(B_N-4x^2)=7.811e-02
  N=30 x=1/7 : Delta=1.206838e+01  4x^2=8.163265e-02  B_N=4.486561e+02  (Delta-4x^2)/(B_N-4x^2)=2.672e-02
  N= 2 x=2/5 : Delta=6.400000e-01  4x^2=6.400000e-01  B_N=2.876416e+00  (Delta-4x^2)/(B_N-4x^2)=0.000e+00
  N=10 x=2/5 : Delta=2.788926e+01  4x^2=6.400000e-01  B_N=1.595443e+03  (Delta-4x^2)/(B_N-4x^2)=1.709e-02
  N=30 x=2/5 : Delta=9.313943e+06  4x^2=6.400000e-01  B_N=3.549655e+09  (Delta-4x^2)/(B_N-4x^2)=2.624e-03
  N= 2 x=1   : Delta=4.000000e+00  4x^2=4.000000e+00  B_N=1.000000e+02  (Delta-4x^2)/(B_N-4x^2)=0.000e+00
  N=10 x=1   : Delta=6.126400e+04  4x^2=4.000000e+00  B_N=3.775693e+07  (Delta-4x^2)/(B_N-4x^2)=1.622e-03
  N=30 x=1   : Delta=2.405863e+16  4x^2=4.000000e+00  B_N=1.337389e+20  (Delta-4x^2)/(B_N-4x^2)=1.799e-04
  4x^2 <= Delta_N <= B_N over even N<=30, 4 values of x: violations = 0; max (Delta-4x^2)/(B-4x^2) = 1.140e-01
=== C3-P7c: recorded (1,0) crossings
  N=   40: u_N=7.2675771726e-02 x*=7.6128439585e-02 u_N sqrt(1+B)=1.9976407998e-01 OK; x*/u_N-1=4.7508e-02 N(x*/u_N-1)/L=0.5151; Delta(x*)=S^2-1=3.5253e-01 B_N(x*)=6.5554e+00; rT*-N(1-p_N)=-0.06731
  N=   80: u_N=4.3120884743e-02 x*=4.4253800351e-02 u_N sqrt(1+B)=1.0193973561e-01 OK; x*/u_N-1=2.6273e-02 N(x*/u_N-1)/L=0.4797; Delta(x*)=S^2-1=2.2101e-01 B_N(x*)=4.5887e+00; rT*-N(1-p_N)=-0.05463
  N=  160: u_N=2.5125664171e-02 x*=2.5493491726e-02 u_N sqrt(1+B)=5.1721251792e-02 OK; x*/u_N-1=1.4640e-02 N(x*/u_N-1)/L=0.4615; Delta(x*)=S^2-1=1.3845e-01 B_N(x*)=3.2374e+00; rT*-N(1-p_N)=-0.04050
  N=  320: u_N=1.4414477303e-02 x*=1.4532059850e-02 u_N sqrt(1+B)=2.6062955194e-02 OK; x*/u_N-1=8.1573e-03 N(x*/u_N-1)/L=0.4525; Delta(x*)=S^2-1=8.6076e-02 B_N(x*)=2.2693e+00; rT*-N(1-p_N)=-0.02817
  N=  640: u_N=8.1597160920e-03 x*=8.1966580004e-03 u_N sqrt(1+B)=1.3077585756e-02 OK; x*/u_N-1=4.5274e-03 N(x*/u_N-1)/L=0.4484; Delta(x*)=S^2-1=5.2941e-02 B_N(x*)=1.5687e+00; rT*-N(1-p_N)=-0.01870
  N= 1280: u_N=4.5662204322e-03 x*=4.5776284592e-03 u_N sqrt(1+B)=6.5626889122e-03 OK; x*/u_N-1=2.4984e-03 N(x*/u_N-1)/L=0.4470; Delta(x*)=S^2-1=3.2168e-02 B_N(x*)=1.0656e+00; rT*-N(1-p_N)=-0.01199
  N= 2560: u_N=2.5301181096e-03 x*=2.5335844970e-03 u_N sqrt(1+B)=3.3090608180e-03 OK; x*/u_N-1=1.3700e-03 N(x*/u_N-1)/L=0.4469; Delta(x*)=S^2-1=1.9307e-02 B_N(x*)=7.1052e-01; rT*-N(1-p_N)=-0.00748
  N= 5120: u_N=1.3900176101e-03 x*=1.3910555095e-03 u_N sqrt(1+B)=1.6824680470e-03 OK; x*/u_N-1=7.4668e-04 N(x*/u_N-1)/L=0.4476; Delta(x*)=S^2-1=1.1451e-02 B_N(x*)=4.6505e-01; rT*-N(1-p_N)=-0.00457
  N=10240: u_N=7.5804880676e-04 x*=7.5835551017e-04 u_N sqrt(1+B)=8.6399678662e-04 OK; x*/u_N-1=4.0460e-04 N(x*/u_N-1)/L=0.4487; Delta(x*)=S^2-1=6.7169e-03 B_N(x*)=2.9906e-01; rT*-N(1-p_N)=-0.00274
  P7c violations = 0
```
Verdicts: C3-P7a: 0 mismatches between the two exact DPs (N <= 12) and 0 violations of 4x^2 <= Delta_N <= B_N (even N <= 30, four x), SURVIVES. C3-P7c: 0 violations of u_N <= x* <= u_N sqrt(1 + B_N(x*)) at the nine recorded (1,0) crossings, SURVIVES.
C3-P7b: NOT RUN (open).

### C3-P8, N = 640: verbatim output (out/C3_fix_p8_run.txt)
```
(r,s)=(0.55,1.0) N=640: T*=4.20946790 sT*=4.20946790 tau_N=0.6514724 EWshare=0.34916286 4dir/corner=0.3016743 rho_N=-0.026634 rho*T=-0.11212 tail/corner=3.5e-36 |Fourier/corner-1|=2.5e-13 [9s,3s]
```
Verdicts (hand evaluation from this line, with Paper A N(1-p_N) = 5.179951 at N = 640, L = log 640 = 6.461468):
- T*_640 = 4.2094679 in [4.18, 4.28]: SURVIVES. S_640(u*) = 0.3491629 in [0.32, 0.38]: SURVIVES.
- l = log(1 - 0.6983257) = -1.198407. D_N = 2.1*4.2094679 - 2*5.179951 - l = 8.839883 - 10.359902 + 1.198407 = -0.321612.
  pred_with = -0.389465 + [0.194733 - 0.138563 - 0.25 + 0.599204]/6.461468 = -0.327281. R_N = D_N - pred_with = +0.00512, in [-0.03, +0.04]: SURVIVES.
  pred_without = pred_with + l/(2L) = -0.419462. |D_N - pred_without| = 0.0978 >= 2|R_N| = 0.0102: SURVIVES.
- Theorem 9 ratio: c_N = (1/4)(1 - 2.1*4.2094679/640)^639 = 3.45230e-5, o4 = 0.3016743*c_N = 1.041469e-5, N^2 o4 = 4.265856, 2(r+s)T*/pi = 4.153738, ratio = 1.0270, in [1.00, 1.06]: SURVIVES.
- S_1280/S_640, S_2560/S_1280, and R_N at N = 1280, 2560: NOT RUN (open).

### Corrections and process notes (2026-09-26)

- The disclosure line of the revision round names code/C3_fix_uniform.py. That script was never written. The D_N comparisons quoted in C3.md (Sections 4.6, 4.7) come from the two audit reports plus hand checks recorded in C3.md; no prediction was attached to them.
- Caveat raised by the recomputation audit, accepted: this ledger has a single file modification time, so the time of individual entries cannot be verified from the file alone; output-file timestamps are consistent with the recorded order (C3_predict.txt 20:01 < C3_run_new.txt 20:08; predict_switch 20:11 < run_switch 20:13; predict_big 20:25 < run_big 20:35; this round: ledger 00:26 < fix outputs 00:28).
- Caveat, accepted: the disclosed engine validation evaluated (1,0) at N = 40, T = 2.7667 and N = 80, T = 3.2865, within 5% and 1% of the later crossings 2.643 and 3.252, which reveals the side of those crossings. The only predictions for these two cells were the non-binding N = 40, 80 delta-bands and the rigorous bound T* >= T_A, so no binding verdict is affected.
