# Predictions, written before any computation (2026-10-25)

Notation. Q irreducible generator on [d], pi its stationary law, D = diag(pi),
e = sqrt(pi), G = D^{1/2} Q D^{-1/2} (so G e = 0 = e^T G), S = (G + G^T)/2,
K = (G - G^T)/2. The stationary data are F_Q(lam) = pi (diag(lam) - Q)^{-1} 1
= e^T (Lam - G)^{-1} e, a rational function of lam in C^d. The occupation
Laplace transform is L(s, w) = F_Q(s 1 + w). The second-moment data are pi
and sym(G^m), m >= 1.

Paper input: the d = 4 example after Theorem 2.5 (sec_minors.tex), with
X = {1,2} and the cut-transpose generator point Q'.

P1 (plan reproduction). For the paper's d = 4 example, F_{Q*} = F_Q exactly
and F_{Q'} != F_Q. The first n with pi (Q - W)^n 1 != pi (Q' - W)^n 1 is
n = 3, the difference sits on w1 w3, w1 w4, w2 w3, w2 w4 only, with
coefficients +-29/9673 (up to the factor convention of the plan).
Q and Q' have the same pi.

P2 (gluing formula). For a cut X | Y in symmetrized coordinates, normalized
so that the rank-one factors satisfy x1.e_X = x2.e_X and y1.e_Y = y2.e_Y,
the "flip" of Y (transpose G_YY, swap y1 and y2) is the generator point of
the cut-transpose, and
    F_Q - F_{flip_Y Q} = (p1 - p2)(q1 - q2) / (1 - alpha beta),
with p1 = e^T M_X^{-1} x1, p2 = x2^T M_X^{-1} e, q1 = y1^T M_Y^{-1} e,
q2 = e^T M_Y^{-1} y2, alpha = x2^T M_X^{-1} x1, beta = y1^T M_Y^{-1} y2,
M_X = Lam_X - G_XX, M_Y = Lam_Y - G_YY. Exact check on the d = 4 example.

P3 (counterexample to O1(a) as stated). d = 5, X = {1,2,3}, Y = {4,5}.
Every state of X leaves X at the same rate with the same landing law on Y,
and every jump from Y into X lands with law pi_X / pi(X); Q_X is not
reversible and the Y half is not symmetric. Then Q' = Q with its X block
replaced by the pi-reversal of that block is a cut-transpose point with
Q' != Q, Q' != Q*, and F_{Q'} = F_Q identically. So the stationary law of
O(T) is the same for every T, and the discrete counts agree for every N.
I expect this to hold exactly (zero rational function).

P4 (d <= 4 second moments). For d <= 4, pi, sym(G), sym(G^2) determine Q up
to reversal for every irreducible Q (K has rank <= 2 on e-perp, so K^2
fixes K up to sign). Check: on the d = 4 example, K'^2 != K^2 or
S' != S for Q'.

P5 (generic d >= 5). For random rational Q with d = 5, 6, 7, the data
S, sym(G^2), sym(G^3) reconstruct G up to transpose by the sign-propagation
algorithm (K^2 eigenplanes, signs from K S K). I expect success in every
random trial and failure on the P3 example (where the K-plane of the X
block is not coupled to the rest by S).

P6 (balanced halves). The condition p1 == p2 forces x1 = x2 and
K_ij (rho_i - rho_j) = 0 (rho = x/e). I predict these two conditions are
NOT sufficient in general: a random X half of size 4 with a two-valued rho
and K supported on the three-state level set will have p1 != p2, unless that
level set is itself a memoryless block of the whole chain.

P7 (one T versus all T). I expect a proof that the law of O(T0) for a single
T0 > 0 already determines the law for every T, from any start. For the
discrete counts at one fixed N this fails: N = 2 only sees pi and the
symmetrized fluxes, so any d = 3 non-reversible Q has a one-parameter
family of Q' with the same N = 2 law.
