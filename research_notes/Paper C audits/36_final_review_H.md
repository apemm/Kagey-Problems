# Final review H: sec_complete, sec_vertex, app_complete, app_vertex

Checked every statement against its proof. No mathematical errors found. Three wording changes, no trims (nothing repeated without adding content).

1. sec_complete.tex, Theorem (balanced crossings) (iii)
   - Old: "The value $T_{N,k}=N(1-p_{N,k})/(d-1)$ of $T$ at the crossing satisfies"
   - New: "As $N\to\infty$, the value $T_{N,k}=\dots$ of $T$ at the crossing satisfies"
   - Reason: the O(1/L) expansions are asymptotic, and the proof uses Theorem crossing(i), which needs large N. The hypothesis was dropped.

2. sec_vertex.tex, last paragraph
   - Old: "In Theorem~\ref{thm:vertex-uniform-root}, $w$ is of order one,"
   - New: "In Theorem~\ref{thm:vertex-uniform-root} with fixed rare counts, $w$ is of order one,"
   - Reason: $w=bu^2\approx y_a\in[1/(|a|+1),1]$ is of order one only for fixed rare counts.

3. sec_vertex.tex, paragraph after the theorem
   - Old: "Lemma~\ref{lem:vertex-randomization} gives $S_{(b,a)}(\sqrt{y/b})\to\mathcal B(y)$"
   - New: "... implies ..."
   - Reason: the lemma states the exact identity and the moment generating function. The limit follows from them (mean and variance of $v\mathcal X$) but is not stated in the lemma.
