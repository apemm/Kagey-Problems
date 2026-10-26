# 36 Final review of app_torus.tex (Appendix A)

Each change: old, then new, then reason.

1. Lemma perron, last sentence.
   Old: "and $\Sigma$, which is $\Gamma$ without the row and column of state $1$, is positive definite."
   New: "and the matrix $\Sigma$ obtained from $\Gamma$ by deleting the row and column of state $1$ is positive definite."
   Reason: Sigma was used before it was defined; the old phrasing read as if Sigma were already known.

2. Prop constant(a), Step 1.
   Old: "which we call the shift property. It is a simple eigenvalue ..."
   New: "... The Perron root is a simple eigenvalue ..."
   Reason: "It" had no clear antecedent (the shift property).

3. Lemma torus-complex, statement.
   Old: "... dominated term by term in modulus by those of X-bar, g-bar, b-bar at s', in place of having nonnegative coefficients."
   New: "... series no longer have nonnegative coefficients, but they are dominated term by term in modulus by those of ... at s'."
   Reason: the old clause was ungrammatical about what replaces what.

4. Local law (a), derivatives of g.
   Old: "Then the first equation is $g_j=-\alpha_j/\alpha_1$, so ..."
   New: "Then the first equation gives $g_j=-\alpha_j/\alpha_1$, so ..."
   Reason: the equation is not equal to a value, it yields it.

5. Local law (a), Regularity.
   Old: "Covering K by finitely many such sets shows that their phi-derivatives are jointly continuous on K x T."
   New: "So their phi-derivatives are jointly continuous on K x T, and covering K by finitely many such sets bounds them there."
   Reason: continuity is local; the covering gives the uniform bound that the Laplace lemma needs. The old sentence attributed continuity to the covering.

6. Proof of Lemma discrete, Step 2.
   Old: "Let n_min = min n_i. We claim that ..."
   New: "Let n_min = min n_i, and let N be so large that hq_max <= 1/2, which is possible since h <= N^{-1/2}. We claim that ..."
   Reason: the proof uses log(1-x) >= -x-x^2 for x <= 1/2 in Step 2, but the bound hq_max <= 1/2 was only stated in Step 4, and the lemma itself does not assume it.

7. Proof of Lemma discrete, Step 2, case m_i > n_i.
   Old: "Then kappa_m = 0, while ..."
   New: "Then the m-th term of Lemma runs is 0, so kappa_m = 0, while ..."
   Reason: kappa_m is defined as the ratio of the m-th term to v_m, and the formula for it does not give 0 when m_i > n_i. The convention is now stated.

8. Proof of Theorem local(b), integral paragraph.
   Old: "The logarithm has no branch on the whole torus when ..."
   New: "The logarithm has no continuous branch on the whole torus when ..."
   Reason: a branch exists pointwise; what fails is a continuous one.

9. Trim, after Theorem local(a).
   Old: "... graph of A_F. Section~\ref{sec:boundary-layer} needs it for other weights."
   New: "... graph of A_F."
   Reason: the same pointer to the boundary-layer section appears in the paragraph before Lemma torus-complex.

No label, \ifarxivbuild branch, statement or proof step was removed. No recomputation was done. All steps of the lemmas were checked against their statements, and no other mismatch was found.
