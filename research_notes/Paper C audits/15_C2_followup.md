# Paper C audit 15. Follow-up pass on Paper C2 after the editor check

October 24, 2026. Manuscript `kagey-problems/problem131/paperC2/problem131_reconstruction.tex`.
Inputs: audit 14 (the editor check and its list of problems not fixed), audit 12 (the split), the
C1 sources `paperC/sec_firstorder.tex` (Theorem 4.2, Remark 4.3), `paperC/EXPORTS.md` and
`paperC/README.md`, and `C theorems 5 and 7/03_T5_numerics.md`.

## 1. Theorem 2.5 and uniformity in tau

C1 states Theorem 4.2 as follows. Part (ii) gives, for an admissible face, upper and lower bounds
on log M_F with constants kappa, T_0, N_0, valid for N >= N_0 and T_0 <= T <= N^(1/3). Part (iii)
is the selection rule at fixed tau, for every start. Remark 4.3 gives the field form: the upper
bound of (ii) with lambda_F(v_F), the matching lower bound for (H) faces from Theorem 5.7, and
(iii), (iv) for fixed tau and v when mu has full support.

C2's Theorem 2.5 now reads, in `sec_prelim.tex`:
(a) the upper bound of C1 Theorem 4.2(ii) in the field form of Remark 4.3, in the variable T on
T_0 <= T <= N^(1/3), and M_F = 0 off the admissible faces;
(b) at fixed tau, with v = 0 or a full-support start, the log of the weighted maximum is
-L min Phi_{tau,v} + O(log L) and for large N every maximizer sits on a minimizing face.
One sentence after it gives the C1 parts and says that every use of (b) is at a fixed tau. The old
(b) (equality for (H) faces) is no longer stated there. Where it was used, Theorem 2.8 (C1 Theorem
5.7) gives it directly.

Every use of Theorem 2.5 in C2, with the decision.

| Where | What is used | Fixed tau suffices |
|---|---|---|
| Prop 4.1 (controlled score law), proof | upper bound and equality for irreducible faces | yes. Prop 4.1 was stated over a compact interval of tau. It is now stated at fixed tau > 0. Its proof uses (a) at T = tau L and Theorem 2.8 with the single field v. |
| Lemma 4.2(b), Lemma 4.5, Prop 4.6, Thm 4.7 | Prop 4.1 at single points (tau, v), with N_0(omega) | yes |
| Lemma 5.1, Thm 5.2 proof | Prop 4.1 at each point of the design ranges, pointwise | yes. The finite-horizon Theorem 5.7 uses Prop 5.6 (C1 Prop 5.16), which is uniform on the class, and never Theorem 2.5. |
| Section 6 opening, Thm 6.2, Thm 6.4, Example 6.6 proof | (b) with v = 0 at tau = e^(h/eta) or x e^(gamma/eta), at fixed eta (and fixed x in Thm 6.4, whose N-threshold already depends on eta and x) | yes |
| Section 6.2, Remark 6.14 | Prop 4.1 at fixed eta, tau = e^(h/eta) and v(eta) | yes |

Decision: no use needs uniformity in tau, so no new lemma was added. For the record, uniformity
of the old (a) and (b) on a compact interval would follow from what C1 states (Theorem 4.2(ii) is
uniform in T on [T_0, N^(1/3)], and Theorem 5.7 is uniform for 1 <= T <= N^(1/3)). The support
claim of the old (c) is not uniform on an interval that contains a tie of two scores, since the
O(log L) errors decide near the tie. That claim was never used uniformly.

Lowtemp references `thm:first}(c)` changed to `(b)` at the four places.

## 2. Lemma 4.5

`sec_modal.tex`, proof of `lem:exposure`.
- The neighbourhood: the strict inequalities hold with 2 delta on an open set around v^0, and U
  is a ball around v^0 whose closure lies in that open set. Then tau_1 > 2 delta on the compact
  closure, so tau_- > delta, and tau_+ is finite.
- The positive constant kappa: lambda_H - lambda_F is bounded below by a positive constant on the
  compact closure (Lemma 2.2), which the old text took for granted.
- The empty case P = G' cap F: the old text bounded Phi(G') by tau_- bar v_1 and then enlarged the
  threshold to bar v_0. It now says that bar v_0 also serves in Lemma 4.4 (its last clause), so
  Phi(G') >= tau_- bar v_0.
Checked against Def 4.3: O is open in Omega (U open, the strict bound on v_j, and the band
|tau - tau_1(v_F)| < delta with tau_1 continuous, and tau > delta > 0). (i) gives a unique
minimizer over all admissible faces at every point of O off the hypersurface, which is what
Prop 4.6 needs (density of S_Q' in O, then continuity of the scores). The singleton step of
Prop 4.6 was also checked (pair at least 1/2 above the better singleton for tau <= bar tau).

## 3. Notation

| Collision | Change |
|---|---|
| G graph (Sec 5) against G face (Sec 4, 6) | the graph is now (V, E), "the graph E". Changed in Section 5 throughout: setting, Thm 5.2, Thm 5.3 and its proof (Q_G is now Q_E), Thm 5.5, the class of Section 5.4, Prop 5.6, Thm 5.7 and its proof. |
| Delta_ij (Thm 5.2) against the simplices Delta_F | s_ij = xi_bar - x_i + x_j, with t_ij = (sqrt(s_ij^2 + 4 w_ij) + s_ij)/(2 w_ij) and w_ij = s_ij/t_ij + t_ij^-2. The stability proof had a_ij for the same quantity, now s_ij. The proof of Thm 5.2(b) uses p = q_i - xi_bar and q_j in place of a and c. |
| s in Sec 5 (s = tau_0 L/N in Thm 5.7, s in Lemma 5.1 proof, s in Thm 5.3 proof) | Thm 5.7(a) writes (N - tau_0 L q_1)/(N - tau_0 L q_i). Lemma 5.1 proof uses u. Thm 5.3 proof says "-B plus a large multiple of I". |
| c in Sec 5 | c = q_j in Thm 5.2 proof removed. c N^(-m*) in Thm 5.7 proof is now C^(-1) N^(-m*). c_kl in the stability proof is chi_kl. The scalar c in phi_hat = c phi + z is a. c(K) in Rem 5.4 is comp(E'). c_ij stays (the finite-horizon constant). |
| K in Sec 5 | K = F \ {i,j} in the proof of Lemma 5.1 is A. The comparison graph K of Rem 5.4 is (V, E'). K_F and K_ij stay (the constants). |
| E error term in Prop 5.6 and E_N(T) in the proof of Thm 5.7, against the edge set E | Prop 5.6(b) states the relative error directly, Thm 5.7's proof writes the bound on Lambda_N(T) + L - Xi(T) - kappa. |
| tau_+ in Prop 4.6 (singleton step) against tau_+ in the proof of Lemma 4.5 | bar tau. |

Scripts: `verify_reconstruction.py` (docstring items 1 and 3, the symbolic check of the inversion
formula now in s_ij, the message "reversible generators on the graph E") and
`verify_finite_horizon.py` (the function t_limit, whose comment still named the old d_i). Section 7
names none of these symbols.

Not changed: E is also the diagonal similarity of Section 3 (outside the editor's list), and the
docstring of `verify_reconstruction.py` still calls the 3-cycle products c, c' (the paper's omega,
omega').

## 4. Least admissible N

New script `paperC2/verify_threshold.py` (standard library, under a second), listed in
`verify_all.py` and in `README.md`, output `data/verify_threshold_output.txt` with the sha256
header (ce29c53c...). Admissible means that the transition matrix I + (T/N)Q of the paper is
stochastic at every tau in [1/(4R), U]. This is N >= U q_max log N. The script finds the least such
N for a 3-state path (q_12 = 1, q_23 = b, R = 3) and a 3-state triangle with one weak edge (R = 4),
b = 2^-1, ..., 2^-8. It checks ||S||_2 <= R and min sqrt(w) = b, stochasticity on a 201-point tau
grid at N and failure at N - 1, and that no smaller N works. It prints N b^2 (the ratio against
b^-2) and N b^2 / log N. Results: N b^2 / log N = 8 R q_max to within 1/(c log N), and N b^2 grows
slowly (path 248 to 412, triangle 485 to 1161), with N growing by a factor 4.0 to 4.8 when b is
halved. So N grows like b^-2 log(1/b), not like b^-2 exactly.

The sentence after Thm 5.7 now says exactly that: I + (T/N)Q is stochastic on the whole range
exactly when N >= U q_max log N, so the least such N has N b^2 / log N = 8 R q_max up to rounding
and grows like b^-2 log(1/b) when q_max stays of order R, with a pointer to Section 7. The
sentence on exact three-state computations (faces with a suppressed state closest near N of order
bar v T) rested only on the research notes and was removed. Section 7 has one sentence on the new
script.

## 5. Bibliography

`paperC1`: "A. Pemmasani, Occupation counts of rarely switching Markov chains: stratified local
laws, crossings and the boundary layer. In preparation, 2026."

## 6. Cover letter

Unchanged, with the arXiv placeholder.

## 7. Build, scripts, length

The edits first gave 41 pages. Prose was tightened to return to 40 with no result, proof step or
example removed: the note after Thm 2.5 and part (a) inlined, the Lemma 4.5 and Prop 4.1 proof
edits kept short, short last lines removed in Sections 1, 3, 4 and 6, inline fractions in the
paragraph after Thm 6.13 and in Section 7 written with a slash, the last clause of Remark 6.14
("so even for a reversible family ...") dropped as a repeat, Section 7 and the data statement
shortened, and the Kim and Landim reference note shortened to "Section 5 is cited with the
numbering of arXiv:2412.13515v2".

Built three times: 40 pages, no undefined references, no multiply defined labels, no overfull or
underfull boxes, no warnings. `py -I verify_all.py`: 5 of 5 PASS (157 s). The .aux, .log, .out
files and the `__pycache__` folder were deleted, and the PDF was kept.
