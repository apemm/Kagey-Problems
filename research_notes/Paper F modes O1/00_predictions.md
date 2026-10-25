# Predictions, written before any computation (2026-10-25)

Notation: zeta law f(n) proportional to n^(-alpha-1); fresh plus start unless
stated; R_N(j) = P_N(N-j)/T_+(N); "sign change" = change of sign of
Delta P_N(k) = P_N(k+1) - P_N(k), zeros skipped.

P1 (plan reproduction, fair start, alpha = 1.5 both signs, N = 2000).
Exactly 5 sign changes, at k near 1, 16, 1000, 1984, 1999 (plan's list).
I expect agreement to within +-1 because of the "position" convention.

P2 (scan N <= 400, fair start). Counts in {1,3,5} only, never above 5.
First N with 5 changes: 60 (alpha 1.2), 98 (1.5), 152 (1.8), 162 (1.9/1.3).
Again +-1 tolerance for convention differences.

P3 (runs >= 2, alpha = 1.5, fresh plus, N = 3000). Delta u_- changes sign
at j = 1..12 and R_N(j) changes direction at j = 1..12 and once more near
j = 28.

P4 (new; difference form of the renewal theorem). Under (RV)+(SPAN),
(u(j) - u(j-1)) * mu^2 / T(j) -> -1. For the zeta law with alpha = 1.5 the
ratio at j = 10^4 should be within 0.1 of -1 (slow convergence expected).
Consequence: for every fresh start, u_- is eventually strictly decreasing.

P5 (new; second-order layer differences). For the zeta law, alpha = 1.5,
fresh plus, the differences satisfy
N*(R_N(j+1) - R_N(j)) ~ N*(u(j+1)-u(j)) + (C(j+1)-C(j))
for j up to a few times j*_N, with relative error that shrinks with N.
The sign change of R_N(j+1)-R_N(j) sits within +-2 of the sign change of
Delta u(j) + Delta C(j)/N.

P6 (new; prepared starts, log-convex law). Zeta law alpha = 1.5, initial run
plus with law f_+ w.p. 1/2, minus of fixed length 5 w.p. 1/2. Profile
kappa(0) = 1/2, kappa(j) = u(j)/2 + u(j-5)/2 1{j>=5}: local min at j = 4,
local max at j = 5. Prediction: for N = 2000 the law has one more local max
and one more local min at the plus end than the fresh law (local max at
N-5), so 4 local maxima in total if the minus end is fresh-like.

P7 (new; prepared start with kappa eventually increasing). Minus initial
run with nu_-(d) = T_-(d)/sum_{d'>=2} T_-(d') for d >= 2, nu_-(1)=0, at
probability 1. Then Delta kappa(j) ~ (c mu - 1) T(j)/mu^2 with
c = 1/(mu-1) > 1/mu, so kappa increases to 1/mu from below eventually.
Prediction: at the plus end there is no antimode at distance of order
N^(1/alpha); the plus-side minimum of P_N(N-j) over 1 <= j <= N/2 stays at
bounded j as N grows.

P8 (new; (LR) is not enough for monotonicity in the big-jump zone). If f_+
carries relative wiggles of size eps at scale w with B_N << w and
eps*L/w large, P_N has extra local extrema inside the big-jump zone even
though P_N/G_N -> 1. Test: f_+(n) ~ n^(-2.5) (1 + 0.3 sin(2 pi n/60)),
N = 3000: many sign changes of Delta P_N between the bulk and the antimode.
