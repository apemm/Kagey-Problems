# Discrete boundary layer (C1, item O1): predictions

Written 2026-10-25, before any code was run. Paper labels refer to
`kagey-problems/problem131/paperC` at commit 3b3a446.

## Setting

F irreducible, i in F, G = F\{i} satisfies (H), n with support F, N' = N - n_i,
n-hat = n restricted to G, beta = n-hat/N', S = hN' (the facet time),
p_i = 1 - h q_i. Lambda~(z) = C_G(beta,z)/C_G(beta,0) * exp(S(J_G(beta) - J_G(beta,z)))
with the functions of Theorem L-facet.

Conjectured discrete kernel:

    L_beta(n_i, N') = (h / 2 pi i) \oint (p_i + h/z)^(n_i - 1) Lambda~(z) dz / z^2
                    = sum_{K=1}^{n_i} binom(n_i-1, K-1) p_i^(n_i-K) h^K [z^K] Lambda~(z).

## Predictions

P1. (Exact lemma.) Lemma layer-exact-discrete holds to rounding, checked against a
    transfer-matrix recursion of my own, for a pair face and for a facet with 3 states.

P2. (Normalization.) P_N(n)/P_{N'}(n-hat) ~ h * K_beta(x, S): exactly one power of h
    for every k, the continuum kernel being a density in x. No extra powers of h for
    k >= 3. The kernel is evaluated at the facet time S = hN', not at T - x.

P3. (Pair face, exact.) For k = 2 the facet chain has one state and
    R = P_N(n)/P_{N'}(n-hat) is a terminating double binomial sum (discrete Pedler).
    Against the Laguerre kernel L, |R/L - 1| = O(h + (T^2/N) sqrt(n_i/N)), with no 1/T
    term and no lower bound on T.

P4. (Lattice regime.) For k = 2 at T = sqrt(N') and n_i = 1..6, R/L - 1 -> 0 as N grows,
    while R/(h K(h n_i, S)) - 1 stays of order 1 (negative, roughly -omega S h/2 when
    n_i is large; between 0 and -omega S h/2 by the Laguerre-Bessel lemma).

P5. (k >= 3.) |P_N(n)/(P_{N'}(n-hat) L) - 1| <= C(1/T + T^2/N). At fixed T it settles,
    as N grows, to a limit of order 1/T (the continuum facet error of Theorem L-facet).

P6. (Lattice vs continuum kernel.) When T^2/N is small, L = h K_beta(x, S)(1 + O(T^2/N))
    for both x = h n_i and x = h(n_i - 1), uniformly down to n_i = 1. So in the range
    T <= N^{1/3} of Theorem A the lattice kernel and the continuum kernel are
    indistinguishable within the error. This contradicts the plan's expectation that
    they differ at n_i = O(1); the difference needs T^2/N of order 1.

P7. The contour value of L does not depend on the radius (sanity check of the
    numerical continuation of J_G and C_G to complex z).
