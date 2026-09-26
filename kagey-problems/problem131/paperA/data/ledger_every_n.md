# Ledger: Paper A crossing for every N (task EN)

Notation. N >= 2 steps, L = log N, c_0 = (1/2) log(pi/8), psi(z) = z + (1/2) log z,
zeta_N = the root of psi(zeta) = L + c_0 (equivalently zeta_N = W_0(pi N^2/4)/2),
u_N = (1-p_N)/p_N (root of S_N(u) = 1), w_N = N u_N, z_N = N(1-p_N) = w_N/(1 + w_N/N),
err_N = z_N - zeta_N - 1/(8 zeta_N), E(z) = sqrt(pi z/2) e^{-z} (I_0(z) + I_1(z)).

## 2026-09-26. Predictions, written before any code for this task was run

State of knowledge when writing: only Paper A's Table tab:pn (p_N for N <= 12, 20, 50, 100, 200, 400)
and hand arithmetic from it. Values at N = 2, 3, 4, 5, 10, 20, 100 below were computed by hand from
that table and are therefore NOT blind; the values at N = 1000 and 10^4 are blind.

Hand values from the table (not blind): err_2 = -0.103, err_3 = -0.050, err_4 = -0.058,
err_5 = -0.048, err_10 = -0.0623, err_20 = -0.0635, err_100 = -0.0423.

Heuristic used for the blind predictions:
err_N ~ -1/(32 zeta^2) + (w - w^2)/(2N) * (1 + 1/(2 zeta))^{-1}, w ~ zeta.

P1 (sign, upper bound). err_N < 0 for every N in [2, 10^4]; i.e. z_N < zeta_N + 1/(8 zeta_N)
    for every N >= 2. Kill: any N in the computed range with err_N >= 0.
P2 (size, blind). err_1000 = -0.0126 +- 0.0010 ; err_10000 = -0.00293 +- 0.00015.
    Equivalently z_1000 = 5.5905 +- 0.0010 and z_10000 = 7.7343 +- 0.0002.
    zeta_1000 = 5.58074 +- 0.00002, zeta_10000 = 7.72101 +- 0.00002.
P3 (sign pattern of z_N - zeta_N). Positive for small N (N <= 12 or so), negative on a middle
    range starting between N = 13 and N = 19, positive again from some N* in [180, 320] on,
    and positive for every N from N* to 10^4. Kill: a third sign change below 10^4, or N*
    outside [180, 320].
P4 (theorem shape). With eps_N := zeta_N (zeta_N + 1)/N + 1/(16 zeta_N^2):
    zeta_N + 1/(8 zeta_N) - eps_N <= z_N < zeta_N + 1/(8 zeta_N) for every N >= 2.
    Analytic proof (uniform Bessel bound + Bessel lemma + elementary estimates) is expected
    to cover zeta_N >= 4, i.e. N >= N_0 = 175. Exact certificates are expected to pass for
    every N in [2, 174], with smallest upper margin (zeta + 1/(8 zeta) - z_N) about 0.032
    (at N = 174) and smallest lower margin about 0.09 (at N = 174).
P5 (where the method itself works). Evaluating the two sufficient conditions exactly
    (with the exact Bessel function, not the lemma), the upper-side condition first holds
    for all larger N from some N between 11 and 20 (it fails at N = 10 by hand estimate);
    the lower-side condition holds for every N >= 2 (using E <= 1 for small arguments).
P6 (Bessel lemma). For every z > 0,
    1 - 1/(8z) - 3/(128 z^2) - 45/(512 z^3) <= E(z) <= 1 - 1/(8z) - 3/(128 z^2) + 15/(512 z^3),
    and numerically E(z) - (1 - 1/(8z) - 3/(128z^2)) ~ -15/(1024 z^3) for large z.
P7 (equation for Paper D). R_N := psi(z_N) - L - c_0 - 1/(8 z_N) satisfies
    -(z_N^2 + z_N)/N <= R_N <= 1/(16 z_N^2) for every N >= 2. R_N < 0 for N from about 15
    to 10^4; heuristically R_N ~ 1/(32 z^2) - z(z-1)/(2N), which changes sign only near
    N ~ 1.7e5 (factor 2 either way).
P8 (runtime). Certificates N <= 174, both exact methods: < 30 s. Exact DP cross-check to
    N = 400: < 2 min. Decimal run-count bisection at N = 10^4: < 1 min. Float DP sign check
    at N = 10^4: < 2 min. Nothing planned over 20 minutes.

## 2026-09-26. Results (verify_every_n.py, output in data/every_n_output.txt)

Run 1 stopped at N = 2 in the certificate loop: u_2 = 1/2 lies exactly on the 1e-9 grid, so
S_2(u_lo) < 1 < S_2(u_hi) cannot hold with adjacent grid points. Fixed by letting the bracket
straddle an exact rational root. Run 2 stopped in section [4b] (Decimal precision lowered below the
1e-45 bracket check in zeta_dec, a script bug). Before stopping, run 2 had finished the certificates
for N = 2..2000 (run-count exact for all, integer DP agreeing for N <= 400):
  "N = 2..2000: all certificates pass; DP agreed exactly for N <= 400.
   smallest upper margin 0.0083206 at N = 2000; smallest lower margin 0.0157452 at N = 2000
   time: run-count 538.6s, DP 9.9s"
Run 3 (final, run-count certificates capped at N = 1000 for time, total 472 s) is the recorded output.

P1 CONFIRMED, now a theorem. err_N < 0 for every N >= 2 (certificates for N <= 174, proof for
   N >= 175). Computed values: err_2 = -0.1030112, err_10 = -0.0623310, err_100 = -0.0422507,
   err_174 = -0.0331935 (smallest upper margin on 2..174, "0.033193 at N = 174").
P2 CONFIRMED. "1000 5.590351166974661 5.590351166975 5.5807388611 -0.0127862" and
   "10000 7.734265514998909 7.734265514999 7.7210118331 -0.0029359" (method 1 = run-count Decimal
   bisection, method 2 = float DP bisection). All four predicted intervals contain the values.
P3 CONFIRMED. "sign(z_2 - zeta_2) = +1; sign changes at N = [16, 219]", both float methods agree for
   every N <= 3000, exact certificates at N = 15, 16, 218, 219 and for every N <= 1000.
   First change 16 (window 13..19), second change 219 (window 180..320).
   New: the theorem itself gives z_N > zeta_N for every N >= N_2 = 2774.
P4 CONFIRMED. N_0 = 175 ("N(zeta=4) = sqrt(32/pi) e^4 = 174.252083839377"). Certificates:
   "N = 2..174: all certificates pass. smallest upper margin 0.033193 at N = 174, smallest lower
   margin 0.085591 at N = 174" (predicted about 0.032 and about 0.09).
P5 CONFIRMED. "up_exact : ... holds for every N in [16, 3000]", "up_lemma : ... [17, 3000]",
   "lo_exact" and "lo_lemma": hold for every N in [2, 3000]. (Upper-side threshold 16 lies in the
   predicted 11..20.)
P6 CONFIRMED. Bounds hold on 2000 grid points z = 0.05..100 and at 19 listed points;
   z^3 (E - 1 + 1/(8z) + 3/(128 z^2)) = -0.014729 at z = 200 against -15/1024 = -0.014648.
   Series vs trapezoid: max difference 7.0e-15.
P7 PARTLY REFUTED. The bounds -(z^2+z)/N <= R_N <= 1/(16 z^2) hold for every N (certificates to
   1000, proof beyond 174). But the onset of R_N < 0 was predicted "from about 15" and is N = 4:
   R_2 = +0.050643, R_3 = +0.040497, R_4 = -0.010778, R_10 = -0.056660, R_10000 = -0.002051.
   The predicted sign change near N ~ 1.7e5 was not tested.
P8 MOSTLY CONFIRMED. Certificates to 174 and DP to 400 (10.9 s) fast. Float DP at N = 10^4 took
   1.9 s per evaluation (Python 3.14), far below the estimate, so full DP bisection was done at 10^4
   (147 s). Not predicted: run-count exact certificates to N = 2000 took 539 s, which is why the
   final run stops them at 1000.

## 2026-09-26. Exact sign sweep (verify_every_n_sign.py, output data/every_n_sign_output.txt)

Not pre-registered as a separate prediction, it tests the P3 claim "positive for every N from N* to
10^4" on the range that neither the certificates (N <= 1000) nor the theorem (N >= 2774) covered.
  "N = 1001..2773: S_N(v) < 1 exactly (so z_N > zeta_N) fails at []
   smallest 1 - S_N(v) = 1.044e-02 at N = 1008
   time 775.5s"
So z_N - zeta_N > 0 for every N >= 219 is now proved (exact computation to 2773, Theorem beyond).
Runtime estimate was about 10 minutes, actual 13.

## 2026-09-26. Repair after the read-only audit of EN.md: predictions for verify_every_n_guards.py

Written before verify_every_n_guards.py was written or run. Nothing here is blind in the strict
sense: the audit report quoted several of these numbers, and before writing this entry I read the CSV
once with awk (max R_hi over 4 <= N <= 1000 is -0.010777942 at N = 4; no row with N >= 401 has
dp_checked = 1). The point of the script is to check guards and wording, not to discover numbers.

G1 (rounding guard of verify_every_n_sign.py). For every N in 1001..2773, with u_zeta from the 60-digit
    Newton zeta_N and v = ceil(10^7 u_zeta)/10^7: v - u_zeta > 1e-40, so the branch
    "or D(a)/DEN == uz" of line 28 never fires. The smallest v - u_zeta over the range lies in
    [1e-13, 1e-9] (about 1773 roughly uniform draws on (0, 1e-7], typical minimum 5e-11).
    Kill: any N with v - u_zeta <= 1e-40.
G2 (rounding guard of section [6] of verify_every_n.py). At N = 15, 16, 218, 219 both
    u_zeta - aa/10^30 and (aa+1)/10^30 - u_zeta exceed 1e-40; smallest of the eight > 1e-34.
    Kill: any of them <= 1e-40.
G3 (sign of z_N - zeta_N from the certificate integers alone). For every 2 <= N <= 1000 the interval
    [z(a/b), z(a'/b)] from the CSV excludes zeta_N; the sign is + for N <= 15, - for 16 <= N <= 218,
    + for 219 <= N <= 1000. The smallest distance from zeta_N to the interval is at N = 218 and lies in
    [1.5e-5, 1.8e-5] (the audit's third method gives z_218 - zeta_218 = -1.7e-5; the interval has
    half-width about 2e-7). Kill: an undecided N, another pattern, or the minimum elsewhere or outside
    the window.
G4 (sign of R_N, for Remark 9). R(z(a'/b)) < 0 for every 4 <= N <= 1000, largest value -0.010778 at N = 4;
    R(z(a/b)) > 0 at N = 2 and 3 (+0.050643, +0.040497). Recomputed in 60-digit Decimal from the CSV
    integers, not from the CSV decimals. Kill: any R_hi >= 0 on 4..1000.
G5 (z_2 <= log 2, for Prop. 5). z_2 = 2/3 exactly (S_2(u) = 2u) and log 2 - 2/3 = 0.02648 +- 0.00001.
    Hand proof: 2/3 < log 2 iff e^2 < 8, and e^2 < 2.72^2 = 7.3984. Second method: Decimal ln 2.
G6 (spot check of the single-method range, and the cost of the full DP). At N = 401, 1000, 1008, 2000,
    2773 with the sign-sweep rational v, the run-count integer and the integer DP agree exactly and are
    < 10^{7(N-1)}; 1 - S_1008(v) = 1.044e-2 (from every_n_sign_output.txt, not blind). DP time from the
    recorded 10.9 s for 798 evaluations with N <= 400, scaled as N^3: 0.85 s at N = 1000 (0.3..3 s),
    18 s at N = 2773 (6..60 s); a full integer-DP sign sweep over 401..2773 would then take >= 1 hour
    (point estimate 3.5 h), above the 20-minute limit, so it is not run.
Runtime of the whole script: under 2 minutes.

## 2026-09-26. Results of verify_every_n_guards.py (output data/every_n_guards_output.txt, 25.5 s)

G1 CONFIRMED. "N = 1001..2773: v = u_zeta exactly at []; smallest v - u_zeta = 1.215e-11 at N = 2652;
   all > 1e-40: True". So the equality branch of verify_every_n_sign.py line 28 never fired.
G2 CONFIRMED. "smallest distance to the 1e-30 grid = 3.173e-31 at N = 15; all > 1e-40: True".
G3 CONFIRMED. "undecided at []; deviations from (+ for N<=15, - for 16..218, + for 219..1000): []",
   "smallest distance from zeta_N to [z(a/b), z(a'/b)] = 1.6562e-05 at N = 218".
G4 CONFIRMED. "max over 4 <= N <= 1000 of R(z(a'/b)) = -0.010778 at N = 4; R(z(a/b)) at N = 2, 3:
   +0.050643, +0.040497".
G5 CONFIRMED. "z_2 = 2/3; log 2 - z_2 = 0.02648051; e^2 = 7.389056 < 8: True".
G6 CONFIRMED. Run-count integer == integer DP and S_N(v) < 1 at N = 401, 1000, 1008, 2000, 2773;
   "N = 1008: ... 1 - S_N(v) = 1.0441e-02". DP times 0.06, 0.75, 0.54, 6.27, 14.80 s (predicted 0.85 s at
   1000 and 18 s at 2773). The observed growth is about N^2.6; integrating it over 401..2773 gives about
   3 h for a full integer-DP sign sweep, so that sweep stays unrun and 401..2773 stays single-method
   in exact arithmetic (the audit's "cost similar to the 775 s sweep" is too low by a factor of about 14).

Script edits made after these results, with no rerun of the long scripts (no printed number changes):
  - verify_every_n_sign.py line 28: dropped "or D(a)/DEN == uz"; the remaining assert
    D(a)/DEN - uz > 1e-40 holds for every N in the range by G1.
  - verify_every_n.py section [6]: added the assert uz - aa/1e30 > 1e-40 and (aa+1)/1e30 - uz > 1e-40
    (holds by G2).
  - verify_every_n.py docstring item 3: "50-digit" corrected to "60-digit" (section [3] runs at prec 60).

Relabelling in EN.md after the audit (no number changed). The earlier line "z_N - zeta_N > 0 for every
N >= 219 is now proved (exact computation to 2773, Theorem beyond)" stands, with this precision added:
the proof is computer-assisted. It uses both exact methods for N <= 400, and the run-count integers
alone for 401 <= N <= 2773, cross-checked there by the two float methods of [6] and by G6. Remark 9's
"R_N < 0 for 4 <= N <= 10^4 (computed)" is corrected. R_N < 0 is certified for 4 <= N <= 1000 (G4) and
computed at N = 10^4. N = 1001..9999 was not computed.

## 2026-09-26. Prediction for G7 of verify_every_n_guards.py (Corollary cor:every-n(d))

Written before G7 was written or run. Not blind: an audit quoted f(zeta_2774) - 1 = 2.1e-4 and
f(zeta_2773) - 1 = -5.2e-6, and one mpmath evaluation at 60 digits gave 2.12433e-4 and -5.21066e-6.
The point of G7 is to print the value the paper quotes, from the script, and to make the step robust
to the 1e-45 bracket on zeta_N.

G7. With g(zeta) = N (1/(8 zeta) - 1/(16 zeta^2)) / (zeta (zeta + 1)) (decreasing in zeta) and zeta
    the 60-digit Newton value of zeta_N, known to within 1e-45: at N = 2774, g(zeta + 1e-45) > 1 and
    g(zeta) - 1 lies in [2.0e-4, 2.2e-4]; at N = 2773, g(zeta - 1e-45) < 1 and g(zeta) - 1 lies in
    [-5.4e-6, -5.0e-6]. Kill: the sign at 2774 not positive, or a value outside these windows.

## 2026-09-26. Result of G7 (data/every_n_guards_output.txt, 16.6 s)

G7 CONFIRMED. "N = 2773: f(zeta_N) - 1 = -5.21066e-06; f < 1 at zeta_N - 1e-45: True" and
"N = 2774: f(zeta_N) - 1 = +2.12433e-04; f > 1 at zeta_N + 1e-45: True". Both values are inside the
predicted windows. The paper now calls this step of Corollary cor:every-n(d) computer-assisted.
