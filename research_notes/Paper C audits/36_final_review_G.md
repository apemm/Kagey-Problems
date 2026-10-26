# Final review G: app_counts.tex and app_laplace.tex

app_laplace.tex: no changes. Hypotheses, uniform forms and the complex Gaussian identity match their proofs.

app_counts.tex changes:

1. Lemma (bridge maxima), part (ii).
   Old: "if $|m^0_i-l\alpha^*_{C,i}|<1$ for all $i$."
   New: "if $|m^0|=l$ and $|m^0_i-l\alpha^*_{C,i}|<1$ for all $i$."
   Reason: $G_C(m^0)$ is defined only for $|m^0|=l$, and the proof of the theorem uses that. The hypothesis was dropped.

2. Proof of Theorem (reducible), step B2 and lower bound. The vector $r_{C_j}$ was named $r$, which clashes with the number $r$ of blocks.
   Old: "$(\mathbf a\cdot r)$", "where $r=r_{C_j}$", "$\mathbf a\cdot r/h^{\varkappa_<}$", "$\mathbf a\cdot r\le$", "$\mathbf a^{\rm c}\cdot r=F$".
   New: the same with $\mathbf r$ in place of $r$.
   Reason: one symbol had two meanings in one proof.

3. Same proof.
   Old: "$\rho_<<R_0$"
   New: "$\rho_<\,<\,R_0$"
   Reason: "<<" reads as "much less than".

4. Lemma (counts-half), Step 2.
   Old: "Let $\sigma=e$,"
   New: "Let $\sigma=\mathrm e$,"
   Reason: $\sigma$ is the number e, and $e$ also appears as a vector elsewhere.

No trims made. Flag, not changed: Theorem (pair-counts)(d) says $\E_e[K(K-1)]\le3U'$ for $e\le1$ from "m is an integer". It holds (bound 2U'), but the one-line reason is terse.
