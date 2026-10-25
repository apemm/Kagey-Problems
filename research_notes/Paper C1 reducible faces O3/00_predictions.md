# Paper C1, item O3: predictions (written before any code)

Date: 2026-10-25. Nothing below has been computed by a script yet.

## The claim under test

Let F be an admissible face with components C_1, ..., C_r, numbered in the order
in which a path visits them (Lemma `lem:admissible`(a)). Put
k_j = |C_j|, lambda_j = lambda_{C_j}, lambda_F = min_j lambda_j, and let k* be the
least k_j with lambda_j = lambda_F (as in Theorem `thm:first`(ii)). Set

    p_F = (k*-1)/2 + k_F - k*,    X = N^{-(k_F-1)} T^{p_F} e^{-T lambda_F}.

P0 (exponent). M_F / X stays between two positive constants for T_0 <= T <= N^{1/3}.

P1 (constant). M_F / X -> K as T -> oo with T <= N^{1/3}, where

    K = max over j with lambda_j = lambda_F, k_j = k*  of  A_j B_j / ((2 pi)^{(k*-1)/2} sqrt(det Sigma_{C_j})),

    A_j = sup over the times of the blocks before j of
          e^{lambda_F (time before j)} mu^T Phi_1 R_1 ... Phi_{j-1} R_{j-1} r_{C_j},
    B_j = sup over the times of the blocks after j of
          e^{lambda_F (time after j)} l_{C_j}^T R_j Phi_{j+1} ... R_{r-1} Phi_r 1.

Here Phi_i(t)_{yx} is the occupation density of the chain started at y, killed on
leaving C_i, that visits all of C_i and ends at x; R_i = (q_{xy}) from C_i to
C_{i+1}; r, l are Perron vectors of Q_{C_j} with l.r = 1; Sigma_{C_j} is the
covariance of Definition `def:tilt` at alpha*_{C_j}. For r = 1 this is K_F.

Mechanism: one block of type (lambda_F, k*) takes time T - O(1) and gives the
Gaussian factor T^{(k*-1)/2}; each other block takes time O(1) and contributes
h^{k_j} (one switch in, k_j - 1 coordinates of size O(1)), hence T^{k_j} after
the factor N^{-(k_j)} is pulled out.

## Test cases (start mu = delta_1 throughout, rates not listed are 0)

E1 (reviewer case). d=3, q12=1, q23=q32=1. F={1,2,3}, C1={1} (lambda 1),
C2={2,3} (lambda 0). k_F=3, k*=2, p=1.5, lambda_F=0.
Predicted K = sqrt(2/pi) = 0.797885 (A=r_2 q12=1, B=l.1=1, det Sigma=1/4).
Maximizer: n_1 = 1.

E2 (long block first, bridge end). d=4, q12=q21=1, q13=1, q34=2. F={1,2,3},
C1={1,2} (lambda=(3-sqrt5)/2=0.381966), C2={3} (lambda 2). k_F=3, k*=2, p=1.5.
Predicted K = alpha*_1 / (sqrt(2 pi) sqrt(det Sigma)) = 0.276393/1.060163 = 0.260708.
This uses the end weight l_1 (not l.1), so it tests the bridge form. Maximizer: n_3 = 1.

E3 (long block in the middle). d=5, q12=1, q23=q32=1, q34=1, q45=3.
F={1,2,3,4}, C={1},{2,3},{4}; lambda of {2,3} = 0.381966, k_F=4, k*=2, p=2.5.
Predicted K = r_2 l_3/1.060163 = 0.447214/1.060163 = 0.421833. Maximizer: n_1=n_4=1.

E4 (two tied components of size 2). d=5, q12=q21=1, q13=1, q25=1, q34=q43=1,
q35=q45=1. F={1,2,3,4}, C1={1,2} and C2={3,4}, both lambda=1. k_F=4, k*=2,
p=2.5 (the bounds of Theorem first(ii) give 2 and 3).
Predicted K = max(K_1, K_2) with K_1 = (1)(1/2)/(sqrt(2 pi)/2) = 0.398942 (if the
sup in B_1 is its value 1/2 at time 0) and K_2 = A_2/(sqrt(2 pi)/2), A_2 = sup of
e^{-t1-t2} sqrt(t1/t2) I_1(2 sqrt(t1 t2)) (expected about 0.37 to 0.45). So we
predict K = K_1 = 0.398942, with the long time in C1 and C2 visited briefly.

## What would kill the claim

- A local log-slope of N^{k_F-1} e^{T lambda_F} M_F in T that settles away from
  p_F (for example at k_F - k* or k_F - 1) as T grows with T^2/N small.
- A ratio M_F/X that drifts like a power of T or log T instead of tending to K.
- In E4, a power above 2.5 (time shared between the tied blocks), or a log factor.

## Paper bounds (for comparison)

Theorem first(ii): k_F - k* <= power <= k_F - 1. E1, E2: [1, 2]; E3, E4: [2, 3].
