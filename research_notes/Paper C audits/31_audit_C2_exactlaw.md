# 31. Audit of Paper C2, Section 4 (the exact occupation law): the two new proofs

Date: 2026-10-25. Object: `kagey-problems/problem131/paperC2/sec_exactlaw.tex` (working tree).
Reference versions: `research_notes/Paper C2 identifiability O1/01_report.md` and `02_audit.md`,
and the integration note `29_C2_O1_integration.md`. Read-only except for this file.

Independent check: `block6.py` in a scratch folder outside the repo, sympy rationals, run with
`py -I`, about 10 s. It does not reuse any repo script.

## Verdicts

| # | Item | Verdict |
|---|---|---|
| 1 | New proof of Theorem 4.12 (`thm:memoryless`), block reversal keeps F_Q | **Proved as written** for every claim except irreducibility of Q^[B]. That sentence is **incomplete**, and one sentence fixes it (below). |
| 2 | Lemma 4.2 (`lem:graph`), the resultant lemma, and its three uses in Theorem 4.3 | **Proved as written** |
| 3 | Statements of Section 4 against the audited versions | **Match.** No unproved claim was added. Three additions are flagged below, and all three are proved in the text. |

---

## Item 1. Reversal of a memoryless block (new proof)

**Claim card.**
- Hypotheses: Q is irreducible and B is a memoryless block (Definition 4.11):
  - Q[B,B^c] = kappa 1 nu^T with kappa > 0 and nu a law on B^c;
  - Q[B^c,B] = c rho with rho = pi_B/pi(B) and c >= 0.
- Q^[B] is Q with Q_B replaced by Q*_B = D_B^{-1} Q_B^T D_B.
- Claims:
  - (a) Q^[B] is a generator with stationary law pi;
  - (b) Q^[B] is irreducible;
  - (c) F_{Q^[B]} = F_Q, hence equal stationary laws of O(T) for all T, and equal count laws
    of I + hQ for all N and admissible h;
  - (d) Q^[B] = Q iff Q*_B = Q_B, which holds when |B| = 2;
  - (e) Q^[B] = Q* when |B^c| = 1.

**Own derivation of the critical step (c).** Write M_B = diag x_B - Q_B and solve
(diag x - Q) z = 1 for x with large entries, so that every matrix below is invertible.
1. Rows B: M_B z_B - kappa (nu . z_{B^c}) 1 = 1, so z_B = (1 + kappa nu . z_{B^c}) M_B^{-1} 1.
   Hence rho z_B = (1 + kappa nu . z_{B^c}) g with g = rho M_B^{-1} 1.
2. Rows B^c: (diag x_{B^c} - Q_{B^c}) z_{B^c} - c (rho z_B) = 1. Substituting rho z_B gives
   (diag x_{B^c} - Q_{B^c} - kappa g c nu^T) z_{B^c} = 1 + g c.
3. Uniqueness. g = O(1/min x) as x grows, so the matrix in step 2 is invertible for large x.
   Then z_{B^c} is the unique solution, a function of g and the data of B^c.
4. F_Q = pi_B z_B + pi_{B^c} z_{B^c} = pi(B)(1 + kappa nu . z_{B^c}) g + pi_{B^c} z_{B^c}.
   So F_Q is a function of g and of (pi, kappa, nu, c, Q_{B^c}).
5. Q^[B] has the same cross blocks and the same pi (by (a)). The definition of memoryless
   uses pi, so B is a memoryless block of Q^[B] with the same (kappa, nu, c).
6. Its g is rho (diag x_B - Q*_B)^{-1} 1. Since diag x_B - Q*_B = D_B^{-1}(diag x_B - Q_B^T) D_B,
   this equals pi(B)^{-1} 1^T (M_B^T)^{-1} pi_B^T = pi(B)^{-1} pi_B M_B^{-1} 1 = g, a scalar
   equal to its own transpose.

This agrees with the text, lines 436 to 445, step for step. The text leaves step 3 implicit
under "x with large entries", and that is enough.

**Implications checked.**
- Flux identity. Sum the columns B of pi Q = 0, using Q_B 1 = -kappa 1 from the rows: this
  gives -kappa pi(B) + sum_y pi_y c_y = 0. Correct.
- pi_B Q_B = -kappa pi_B. The columns B give pi_B Q_B + (sum_y pi_y c_y) rho = 0. Correct.
- (a) Rows of Q^[B]:
  - Q*_B 1 = D_B^{-1}(pi_B Q_B)^T = -kappa 1;
  - the rows B then sum to -kappa + kappa sum nu = 0.

  Columns of pi Q^[B]:
  - columns B: pi_B Q*_B = (Q_B 1)^T D_B = -kappa pi_B, and the inflow is
    (sum pi_y c_y) rho = kappa pi_B, so they cancel;
  - columns B^c: unchanged, since pi_B and Q[B,B^c] are unchanged.

  The off-diagonal entries pi_j q_ji / pi_i are nonnegative. Correct.
- (b) Irreducibility (lines 431 to 434): **gap.** The text says a Q-path stays a Q^[B]-path
  when each sojourn in B is replaced by a single state of B. This handles a sojourn entered
  from B^c (c_y > 0 for the entering state y, so y -> i has positive rate for every i in B)
  and left to B^c (rate kappa nu_{y'} from every state). It also handles a first sojourn
  starting at s (replaced by s) and a last sojourn ending at t (replaced by t).

  It fails for a path from s to t, both in B with s != t, that never leaves B. One sojourn
  would have to become two states. The internal edges of Q*_B are reversed, so that path
  need not survive.

  **Fix (one sentence).** For s, t in B, first jump from s to some y' with nu_{y'} > 0 (rate
  kappa > 0). Then take a Q-path from y' to t up to its first entry into B; it runs inside
  B^c, which is unchanged, and it enters from some y with c_y > 0, so y -> t is an edge of
  Q^[B]. The claim is true: the code below finds Q^[B] irreducible in all 3 draws. Only the
  sentence is short. Nothing else in Section 4 uses irreducibility of Q^[B], except the
  "if" part of Conjecture 4.15, where blocks are reversed in succession.
- (c) The count statement. The diagonals of Q*_B and Q_B agree, so q_max is unchanged and
  "admissible h" means the same for both generators. Lemma 4.1(b) applies. Correct.
- (d) If |B| = 2, then Q_B + kappa I has nonnegative off-diagonal entries, zero row sums and
  rho(Q_B + kappa I) = 0. A two-state generator is reversible for its stationary law.
  Correct.
- (e) B^c = {y}:
  - q*_{iy} = pi_y c_y / pi(B) = kappa by the flux identity;
  - q*_{yi} = pi_i kappa / pi_y = c_y pi_i / pi(B), again by the flux identity;
  - Q*_B is the block, and the (y,y) entry is unchanged.

  So Q^[B] = Q*. Correct.
- Remark 4.13 (not new, but rewritten in Q coordinates). The factors are a = 1, b = kappa nu,
  c/pi(B) and u = pi_B^T, and they satisfy the normalization. Then p1 = p2 = pi_B R_B 1. From
  Proposition 4.8:
  - q''_{iy} = pi_y c_y / pi(B);
  - q''_{yi} = kappa nu_y pi_i / pi_y;
  - Q''_B = Q_B and Q''_{B^c} = Q*_{B^c}.

  Taking the reversal gives (Q'')^* = Q^[B] entry by entry. Correct. Under Definition
  `def:orbit`, the orbit also contains the classes reached from -Q^T, so the last clause is
  consistent with the definition.

**Exact spot check, d = 6** (`block6.py`, seed 31025). Each draw takes a random rational
generator R on B with stationary law rho, random kappa, nu and c (with one c_y = 0 in two
draws), and a random Q_{B^c} (sparse in two draws). Q is built as in the definition, and
Q^[B] from the computed pi. Three draws: |B| = 3 (dense), |B| = 4 (sparse), |B| = 3
(sparse). One sparse draw was reducible and was redrawn. In every draw:

| Check | Result |
|---|---|
| pi_B / pi(B) = rho, and the flux identity | holds |
| Q^[B] is a generator with pi Q^[B] = 0 and nonnegative off-diagonal entries | holds |
| Q^[B] differs from Q and from Q* | yes |
| Q and Q^[B] irreducible (reachability) | yes |
| F_Q = F_{Q^[B]} as rational functions in x_0..x_5: denominator det(diag x - M) and numerator pi adj(diag x - M) 1, expanded symbolically | both equal |
| From the start e_1 the numerators differ | yes |
| At a random rational x: g = g*, z_{B^c} from the reduced system equals the full solve, rho z_B = (1 + kappa nu . z_{B^c}) g, and the F_Q formula of line 441 | all hold exactly |

**Verdict, item 1.** Claims (a), (c), (d) and (e) are proved as written. Claim (b) is true,
but its one-sentence proof is incomplete. The smallest missing implication is the case of s
and t both in B, which needs the path to be routed through B^c first.

---

## Item 2. Lemma 4.2 (vanishing on a graph) and its uses

**Claim card.**
- Hypotheses:
  - P in C[s,w] is irreducible and monic in s of degree d >= 1;
  - U in R^d is nonempty and open;
  - theta: U -> C is any function with P(theta(w), w) = 0, with no continuity assumed;
  - R in C[s,w] vanishes at (theta(w), w) for all w in U.
- Claim: P divides R.

**Own derivation of the critical step.**
1. Division. P is monic in s, so R = A P + B in C[w][s] with deg_s B < d, and
   B(theta(w), w) = 0 on U.
2. No common factor. Suppose B != 0. P is primitive and irreducible in C[w][s], so by Gauss
   it is irreducible in C(w)[s]. Any common factor of positive degree would then be an
   associate of P and would divide B, forcing deg_s B >= d. So gcd(P, B) = 1 in C(w)[s],
   and rho = Res_s(P, B), taken with the true degree e of B and a nonzero leading
   coefficient, is a nonzero element of C[w]. (If e = 0, rho = B^d.)
3. Specialization. For w0 in C^d, the Sylvester determinant specializes entrywise.
   P(., w0) keeps exact degree d (monic), so Res_{d,e}(P(., w0), B(., w0)) =
   prod_i B(sigma_i, w0) over the d roots sigma_i of P(., w0) with multiplicity. This holds
   even if the leading coefficient of B vanishes at w0.
4. Conclusion. theta(w) is among the sigma_i, so rho(w) = 0 on U. The real and imaginary
   parts of rho are real polynomials vanishing on a nonempty open set of R^d, so rho = 0.
   This contradicts step 2, hence B = 0.

This is the text's proof, lines 86 to 94. Every step holds, and the specialization in step 3
is what "since P is monic" covers. No complex continuation is needed, which removes the
routine step that `02_audit.md` asked to have written out.

**The hypothesis on P in the application** (lines 74 to 77):
- P(s,w) = det(sI - Q + W) = R_V(-(s1 + w)).
- R_V is irreducible by Lemma 2.1, and it stays irreducible in C[s, lambda] because it does
  not involve s.
- (s, w) -> (s, s1 + w) is an automorphism of C[s,w].
- P is monic of degree d in s.

Correct.

**The three uses.**
- Step 3. N_mu has s-degree d - 1 and leading coefficient mu . 1 = 1, so N_mu != 0 and P does
  not divide it.
  - Applied to any open U' in U, the lemma shows that N_mu(theta, w) is not identically 0
    on U'.
  - theta is a simple eigenvalue, hence continuous (indeed analytic) on U. A point where the
    value is nonzero therefore gives a ball U_1.
  - partial_s P(theta, w) != 0 by simplicity, so chi != 0 on U_1.

  Correct.
- Step 5. theta' = theta + c on U_1 and P'(theta', w) = 0, so R(s,w) := P'(s + c, w) vanishes
  on the graph.
  - The lemma gives P | P'(s + c, w), and both are monic of degree d, so they are equal.
  - At s = 0: det(-Q + W) = det(cI - Q' + W). So the principal minors of -Q' + cI and of -Q
    agree.
  - At w = 0: spec Q' = spec Q + c. The spectra give c >= 0 (-c in spec Q) and c <= 0
    (c in spec Q'), so c = 0.

  Correct.
- Step 6. P' = P and theta' = theta give chi = chi' on U_1 from (4.1). The equal denominators
  partial_s P(theta, w) then give N_mu(theta, w) = N'_{mu'}(theta, w).
  - The lemma gives P | (N_mu - N'_{mu'}), and the s-degree is below d, so the difference
    is 0.
  - Hence F^mu_Q(s1 + w) = F^{mu'}_{Q'}(s1 + w) as rational functions.

  Correct.

**Also checked (Step 2 was rewritten, not new, but it feeds the lemma).**
- Gershgorin. The eigenvalues of V - eps Q lie within |eps| q_i + |eps| q_i <= 2|eps| q of
  v_i.
- The disks are disjoint when |eps| < delta(v)/(4q), and then by continuity each holds
  exactly one simple eigenvalue.
- eps_* > 0 on the closed ball, by continuity of delta.
- theta is real: its conjugate lies in the same disk.
- The error bound O(e^{-T0 t delta/2}) holds once t delta > 8q, which is enough as
  t -> infinity.

**Verdict, item 2: proved as written.**

---

## Item 3. Statements of Section 4 against the audited versions

| Section 4 | Audited source | Match |
|---|---|---|
| Lemma 4.1(a)-(c) | report Lemma 1.1(i)-(iii) | yes. (b) rechecked: mu yZ (I - yPZ)^{-1} 1 = mu((yZ)^{-1} - P)^{-1} 1 and (yZ)^{-1} - I - hQ = h(diag x - Q). |
| Theorem 4.3 | report Theorem 1 | yes |
| Theorem 4.4 | report Theorem 2 | yes. "Measure zero" is added, and it is immediate from finitely many proper affine subspaces of the hyperplane. |
| Theorem 4.5(i), (ii) | report Theorem 3(i), (ii) | yes (Q' only needs pi Q' = 0) |
| Theorem 4.5(iii) | report Theorem 3(iii) and summary item 2 ("open dense, Lebesgue-full set of generators") | yes. The global statement and the per-pi statement are both in the audited text. The new explicit polynomial is checked: the denominators of P_k are u_k psi'(u_k), each index occurs in r - 1 pairs, tr(P_k S P_l S) = \|P_k S P_l\|^2, and the result is symmetric in the u_k. |
| Theorem 4.6 | report Theorem 4 | yes. The converse F_{Q*} = F_Q is rechecked. |
| Remark 4.7 | report Lemma 1.1(iv) with the audit's N^2 D correction | yes, plus addition A below |
| Proposition 4.8, Corollary 4.9 | report Proposition 5, the side fact, and the criterion | yes |
| Remark 4.10 | report Corollary 5.1 | yes, rechecked in Q coordinates: u_i = pi_i a_i, and coefficient (a_j - a_i)(pi_i q_ij - pi_j q_ji). The size-2 case gives Q*_X = Q_X. |
| Definition 4.11, Theorem 4.12 | report Definition and Theorem 6 | yes. The equality cases are a weaker subset of the report's iff statements. |
| Remark 4.13 | report Theorem 6 step 4 | yes |
| Example 4.14 | report Corollary 7 | yes, plus addition B below |
| Paragraph after the example | report | yes: only "none for d <= 4"; there is no "every d >= 5" |
| Conjectures 4.15, 4.16 and the text after them | report Conjectures A, B | yes. The "if" part and the d <= 4 / no-cut / generic "only if" cases are as audited. Single cut-transposes are not claimed. Conjecture B is translated correctly: x1 = x2 iff u = D_X a, and the support of K_X is preserved by the diagonal scaling. |

**Additions not in the audited text (all proved where they stand).**
- A. Remark 4.7: "for N >= 3 [one N, N - 1 values of h] determine Q up to time reversal when
  d <= 4, and for N >= 4 under (ii)". Proof:
  - E_pi n = N pi gives pi' = pi, so N^2 D is known;
  - the Vandermonde in h^1..h^{N-1} at N - 1 distinct positive admissible h gives
    Sigma_1..Sigma_{N-1};
  - Theorem 4.5 finishes.

  Correct. The audited (iv) said "N distinct values"; N - 1 is right once D is known.
- B. Example 4.14:
  - q*_14 = pi_4 q_41 / pi_1 = (6/21)/(4/21) = 3/2;
  - h <= 1/10, since q_max = q_5 = 3 * 2 + 4 = 10;
  - c = (3, 6) from q_{yi} = c_y / 3.

  All correct.
- C. The paragraph after Theorem 4.6 adds "= (1/2) w^T (Sigma_1 - Sigma'_1) w". Check: in
  pi (Q - W)^3 1, the terms with 2 Q's or 3 Q's vanish (pi Q = 0, Q 1 = 0). Among the
  terms with one Q, only pi W Q W 1 = w^T D Q w = (1/2) w^T Sigma_1 w survives. Correct.
  The integration script also verifies it.

No claim of the "examples exist for every d >= 5" kind appears in Section 4. Theorem B(iv)
in the introduction also says only "for d = 5".

## Recommended edit

Replace lines 432 to 434 with a sentence that also covers s, t in B. For example: "From
s in B jump to some y with nu_y > 0, then follow a path of Q to the first entry into B,
which runs in B^c, is unchanged, and enters from a state y' with c_{y'} > 0, so that y' -> t
is a jump of Q^[B] for every t in B. Paths between states of B^c, or from B^c to B, are
handled the same way."
