# Final review B: sec_model.tex and sec_dv.tex

All other statements and proofs were checked against their claims and left unchanged.

1. sec_model.tex, after Definition faces.
Old: "$\alpha^*_F$ is the long-run law of the visit fractions of the chain conditioned to stay in $F$."
New: "$\alpha^*_F$ is the limit as $T\to\infty$ of the law of the visit fractions of the continuous-time chain conditioned to stay in $F$ up to time $T$."
Reason: the old wording left the time horizon, the limit and the continuous-time chain implicit.

2. sec_dv.tex, opening sentence.
Old: "Every rate in this paper is the restriction of one functional, the Donsker and Varadhan functional of the chain."
New: same, plus "or of its discrete version of Section~\ref{sec:discrete-rate}."
Reason: Section 3.3 introduces J^(h), which is not the continuous functional.

3. sec_dv.tex, after Proposition restriction.
Old: "So the cost of a point of $\Delta_F$ does not depend on the face in which we read it."
New: deleted.
Reason: restates the proposition.

4. sec_dv.tex, before (Jfield).
Old: "Since $\sum_i\alpha_iv_i=v\cdot\alpha$,"
New: "Since $\sum_i\alpha_i=1$,"
Reason: the identity needs the normalization of alpha, not the definition of the dot product.

5. sec_dv.tex, remark after Proposition rate.
Old: "On a face that is not reversible the formula in (c) is only an upper bound, by its proof."
New: "Without reversibility the proof of (c) still gives the formula as an upper bound."
Reason: the old text claimed the formula is only an upper bound, which is more than is proved. The proof gives an upper bound and equality under reversibility.

6. sec_dv.tex, definition of lambda^(h)_{F'}(v).
Old: "For any face $F'$ and $v\in\R^{F'}$ we put"
New: "For any face $F'$, any $v\in\R^{F'}$ and $0<h<1/q_{\max}$ we put"
Reason: the range of h under which the matrix has a positive diagonal was not stated.
