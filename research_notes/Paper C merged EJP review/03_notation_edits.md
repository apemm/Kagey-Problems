# Bounded notation and citation edits

## Which changes were made

### Takeaway
The edits address the assigned notation, domain, citation, normalization, and availability issues in the five owned TeX files. The historical boundary claims are explicitly attributed to version 1 of Paper B. [Section 6](../../kagey-problems/problem131/paperC/sec_vertex.tex)

### Cited Findings
- Remark `rem:B-boundary` now states the conclusion of old Paper B Corollary C.3 under the hypotheses of Theorem C.1. When every rare count is `o(N/(log N)^2)`, its size changes the crossing expansion only by `o(1)`, while the number of rare coordinates still affects the leading and logarithmic coefficients. The other exact citations remain Theorem 6.2 and Remark 6.3 with Theorem C.1. The cached v1 text confirms these numbers and the qualification about the number of rare coordinates. [Edited remark](../../kagey-problems/problem131/paperC/sec_vertex.tex), [old boundary source](../../kagey-problems/problem131/archive/paperB/app_boundary.tex), [cached v1 text](<../Paper A full verification/ising_sources_20261015_c7e2/paperB_v1.txt>)
- The defining sum for `B_n` and its Laguerre identity now occur together once at `eq:refresh-polynomial` in Section 5, with the existing DLMF equation citation 18.5.12. Appendix C and Section 6 refer to that equation. The coefficient expansions used inside the Appendix D proofs remain part of those proofs. [Section 5](../../kagey-problems/problem131/paperC/sec_complete.tex), [Appendix C](../../kagey-problems/problem131/paperC/app_complete.tex), [Section 6](../../kagey-problems/problem131/paperC/sec_vertex.tex)
- Appendix C uses `w` for the polynomial argument, `rho_i` for the local binomial-transform coefficients, and `omega_i` and `omega'_i` for the weights. The later centered crossing coordinate can therefore retain `y`. The local `D_N` alias has been removed in favor of the displayed logarithmic ratio, leaving `D_k` unambiguous. The analogous unnecessary `D_N` reference in the two-state proof has also been removed. [Appendix C](../../kagey-problems/problem131/paperC/app_complete.tex), [two-state proof](../../kagey-problems/problem131/paperC/sec_complete.tex)
- Lemma D.1 now states its elasticity upper bound for every positive `y` and its lower bound only for `0<y<=1`. Lemma D.2 states the Jensen lower bound for every `0<u<1` and imposes `s<1` only on the tangent upper bound. Step 1 of the vertex theorem proof explicitly applies the restricted elasticity lower bound at `y_a<=1` and uses the unrestricted Jensen bound at `u_+`. [Appendix D](../../kagey-problems/problem131/paperC/app_vertex.tex)
- The covariance sentence refers directly to local Definition `def:tilt`. The repeated explanation of `D(alpha)=d C_F(alpha)` now refers to Example `ex:complete-face`. The repeated proof of monotonic winning support size now refers to the comparison in Remark `rem:start-lines`. [Section 5](../../kagey-problems/problem131/paperC/sec_complete.tex), [local definition and complete-face example](../../kagey-problems/problem131/paperC/sec_secondorder.tex)
- Remark `rem:K3-finite` identifies the reported finite widths as widths in `z=Nu`, equivalently in `z-L+(log L)/2` at fixed `N`. It separately identifies the limiting window in `t` and its width `t_ef-a_2`. This matches the archived script's `tcoord` and width calculation. [Edited remark](../../kagey-problems/problem131/paperC/sec_complete.tex), [historical computation](../../kagey-problems/problem131/archive/paperB/verify_general_start.py)
- The sentence following Corollary `cor:weakfield-phases` now adds `(d-1)t+log d` to the general weak-field line. Indeed `ell_F^xi=log K_F-(d-k)t+bar xi_F` and `K_F=D_k/d`, so this addition gives `log D_k+(k-1)t+bar xi_F`, including `k=1` with `D_1=1`. [Corrected sentence](../../kagey-problems/problem131/paperC/sec_complete.tex), [general weak-field proposition](../../kagey-problems/problem131/paperC/sec_secondorder.tex)
- Section 8 defines `z=Nu=T/p` as the normalized switch coordinate and separately recalls `z_N=N(1-p_N)` as the two-state crossing value. The supplement references use `Proposition~\sref{prop:triangles}` for the result and `Section~\sref{app:examples-checks}` for the computational subsection, which is Section S1.3. [Section 8](../../kagey-problems/problem131/paperC/sec_verify.tex), [supplement source](../../kagey-problems/problem131/paperC/supplement.tex)
- Historical script paths now point to `kagey-problems/problem131/archive/paperB`. The nonexistent release claim has been replaced by source revision `5db17e4065c6acfd66e8bea6ba8237c455db5e4d`. The rerun instructions explicitly refer to the original `paperB` and `paperC` folder names at that revision. [Availability statement](../../kagey-problems/problem131/paperC/sec_verify.tex), [pinned source revision](https://github.com/apemm/Kagey-Problems/tree/5db17e4065c6acfd66e8bea6ba8237c455db5e4d)

### Inferences
- Consolidating the polynomial definition in Section 5 gives Section 6 and both appendices an earlier shared definition and avoids another forward reference to an appendix. [Shared definition](../../kagey-problems/problem131/paperC/sec_complete.tex)

### Gaps
- No mathematical gap was identified within the assigned changes. Compilation and layout inspection belong to the parent's integration pass. [Build instructions](../../kagey-problems/problem131/paperC/problem131_switching.tex)

## Which bounded checks were completed

### Takeaway
Source and arithmetic checks passed. No full verification sweep, Lake command, or LaTeX build was run in this task. [Edited manuscript sources](../../kagey-problems/problem131/paperC/sec_verify.tex)

### Cited Findings
- `git diff --check` passed for all five owned TeX files. A source audit found balanced TeX environments, resolved all 170 reference uses in those files to current main or supplement labels, and resolved their bibliography keys. The new shared polynomial label occurs once. [Section 5](../../kagey-problems/problem131/paperC/sec_complete.tex), [Section 6](../../kagey-problems/problem131/paperC/sec_vertex.tex), [Section 8](../../kagey-problems/problem131/paperC/sec_verify.tex), [Appendix C](../../kagey-problems/problem131/paperC/app_complete.tex), [Appendix D](../../kagey-problems/problem131/paperC/app_vertex.tex)
- The new lines were checked for semicolons, prose colons, and em dashes. The renamed Appendix C coefficients and weights were checked for leftover old notation in the balancing proof. [Appendix C](../../kagey-problems/problem131/paperC/app_complete.tex)
- The weak-field normalization was derived algebraically and checked numerically in 54 elementary cases, including vertices. The required additive constant is `log d`. [Weak-field lines and their normalization](../../kagey-problems/problem131/paperC/sec_complete.tex)
- Solving only the two displayed heuristic endpoint equations reproduced the quoted widths `0.0802`, `0.0321`, `0.0226`, and `0.0217` at `N=300`, `3000`, `30000`, and `300000`. The limiting `t` width evaluates to approximately `0.02605800057`. These checks did not recompute any exact finite-chain maximum. [Endpoint equations and reported widths](../../kagey-problems/problem131/paperC/sec_complete.tex)
- The pinned commit resolves locally and contains the original `kagey-problems/problem131/paperB`, `paperC`, and `lean/PaperB` directories. [Pinned revision](https://github.com/apemm/Kagey-Problems/tree/5db17e4065c6acfd66e8bea6ba8237c455db5e4d)

### Inferences
- At fixed `N`, subtracting `L-(log L)/2` is a translation, so the script's finite window width equals the width in `z`. Replacing `log L` with `log z` would change that finite width. [Archived script](../../kagey-problems/problem131/archive/paperB/verify_general_start.py)

### Gaps
- The source audit establishes label existence and environment balance, not successful typesetting or the final rendered numbers. [Main and supplement build instructions](../../kagey-problems/problem131/paperC/problem131_switching.tex)

## What remains for integration and which files were edited

### Takeaway
Only the five assigned TeX files and this note were written. The parent owns the combined build and integration. [Owned manuscript files](../../kagey-problems/problem131/paperC/sec_complete.tex)

### Cited Findings
- Edited `paperC/app_complete.tex`. [File](../../kagey-problems/problem131/paperC/app_complete.tex)
- Edited `paperC/app_vertex.tex`. [File](../../kagey-problems/problem131/paperC/app_vertex.tex)
- Edited `paperC/sec_vertex.tex`. [File](../../kagey-problems/problem131/paperC/sec_vertex.tex)
- Edited `paperC/sec_complete.tex`. [File](../../kagey-problems/problem131/paperC/sec_complete.tex)
- Edited `paperC/sec_verify.tex`. [File](../../kagey-problems/problem131/paperC/sec_verify.tex)
- Added `research_notes/Paper C merged EJP review/03_notation_edits.md`. [This note](03_notation_edits.md)

### Inferences
- The added equation label requires the parent's normal reference-resolution build of the merged main paper and supplement. [Build instructions](../../kagey-problems/problem131/paperC/problem131_switching.tex)

### Gaps
- No unresolved notation or citation issue remains within this assignment. The historical rare-coordinate results remain quoted results rather than newly merged proofs. [Version-specific boundary remark](../../kagey-problems/problem131/paperC/sec_vertex.tex)
