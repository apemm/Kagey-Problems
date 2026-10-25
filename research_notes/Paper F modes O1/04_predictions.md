# Predictions for the fourth round, written before any run (2026-10-25)

Target: the upper bound in Conjecture `conj:three-modes`, in three steps:
(a) the bulk, (b) the antimode window, (c) the big-jump zone.
Notation as in 01-03. D_N(j) = P_N(N-j-1) - P_N(N-j); Delta is the forward
difference in j; Delta^2 P_N(N-j) = D_N(j+1) - D_N(j). Zeta law means
f(n) = n^(-5/2)/zeta(5/2) (alpha = 3/2) for both signs unless stated.

## Analytic expectations that drive the predictions

E1. Second-difference renewal theorem: under (RV), (SPAN), (LR) for the minus
sign, u(j+1) - 2u(j) + u(j-1) ~ f_-(j)/mu_-^2. No (LD) is needed for this.

E2. Second differences in the layer: under (LR), (LD2) for the plus sign
[(LD2): f(n+1) - 2f(n) + f(n-1) = O(f(n)/n^2)], uniformly in 1 <= j <= N^(1-eta),
   Delta^2_j P_N(N-j) = T_+(N) Delta^2 u_-(j) + O( f_+(N) (T_-(j) + 1/N) ).
So j -> P_N(N-j) is strictly convex on J_0 <= j <= N^(2/(alpha_-+1) - eps),
which contains the antimode window.

E3. Difference form of Theorem B: D_N(j) = (1+o(1)) d_j G_N, with
   d_j G ~ 2 s f_+(L)/mu_-^2 + (j s^2/mu_-^3)(alpha_+ + 1) f_+(L)/L,
L = N - j s/mu_-, uniformly on N^(1-eta) <= j <= (1-p)N - K B_N as N -> oo
then K -> oo, when the two scales are comparable.

E4. Bulk: B_N^2 Delta P_N(k) - h_N'(x) -> 0 and B_N^3 Delta^2 P_N - h_N'' -> 0
uniformly on |x| <= R.

## Numerical predictions (to be tested with exact float64 recursions)

R1 (E1). For the zeta law, Delta^2 u(j) mu^2 / f(j) at j = 10, 100, 1000,
10000 tends to 1; within 0.1 of 1 at j = 1000 (rate about j^(1-alpha)).
For runs >= 2 (f proportional to n^(-5/2) on n >= 2), Delta^2 u changes sign
for the last time before j = 30, and the ratio is within 0.1 of 1 at j = 10^4.

R2 (E2). Zeta law, fresh plus, N = 1000, 3000, 10000: the normalized error
   E_N(j) = [Delta^2 P_N(N-j) - T_+(N) Delta^2 u(j)] / [f_+(N)(T_-(j) + 1/N)]
stays bounded, |E_N| <= 100, on 1 <= j <= N^0.9, with no growth in N.

R3. Zeta law, fresh plus, N = 2000: P_N(N-j) is strictly convex in j on the
whole stretch from j = 0 to the inflection point of the bulk on the plus
side (x about +1 in units of B_N), not only in the layer. Same for the fair
start, with j = 0 excluded if needed.

R4 (E3). Zeta law, fresh plus: D_N(j) > 0 on N^0.6 <= j <= (1-p)N - 3 B_N
for N = 1000, 2000, 4000, and the ratio D_N(j)/dG(j) (formula of E3) lies in
[0.7, 1.3] for N^0.7 <= j <= N/4 and moves toward 1 as N grows.

R5 (E4). Zeta law, fair start: sup_{|x|<=3} |B_N^2 Delta P_N - h'(x)|
decreases from N = 1000 to 4000 (slow, maybe like N^(-1/3)), and Delta P_N
changes sign exactly once on |x| <= 3, with Delta^2 P_N < 0 on |x| <= 0.5.

R6 (runs >= 2, fair start, alpha = 3/2). The modes counted with the paper's
convention: 16 at N = 1000, 15 at N = 3000 and 4000 (M_+ + M_- + 1 = 15).
At N = 1000 the extra minimum-maximum pair sits at distance between 15 and 60
from an end, where Delta^2_j P_N(N-j) is not yet positive; at N = 4000 the
second difference is positive on the whole window around the antimode.

R7 (local difference big jump, E3's input). For the zeta law,
   [f^{*m}(n-1) - f^{*m}(n)] / [m (alpha+1) f(L)/L], L = n - m mu,
tends to 1 as K = L/a(m) grows, for m = 10, 100, 1000: within 0.2 of 1 at
K = 20 for every m tested.
