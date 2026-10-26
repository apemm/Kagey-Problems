# 36 Final review of sec_firstorder.tex and sec_verify.tex

All items checked against the scripts in paperC and lean/PaperC/MAP.md, read only. Nothing recomputed.

1. sec_verify.tex, full-range script
   Old: "has $T|R-1|\le0.2$ for $16\le T\le N/4$"
   New: "has $T|R-1|\le0.25$ at points of $[0.45,0.85]$ for $T=16$, $63$, $200$, $400$ and $1000=N/4$"
   Reason: verify_full_range.py asserts 0.25, at those values of T and on that interval only.

2. sec_verify.tex, Lean paragraph
   Old: "MAP.md matches each statement to its Lean theorems."
   New: "MAP.md gives for each statement the Lean theorems that prove it or its finite core, and lists what is not in Lean."
   Reason: MAP.md marks rows "in part" and has a "Not in Lean" list, so "each statement" overclaimed.

3. sec_firstorder.tex, Remark (a field), trim
   Old: "So if $\mu$ has full support, then for fixed $\tau$ and $v$, (iii) and (iv) hold ..."
   New: "So for fixed $\tau$ and $v$, (iii) and (iv) hold ..."
   Reason: the hypothesis "if $\mu$ has full support" is stated in the sentence just before. Repeated.

4. sec_firstorder.tex, definition of $S^*$
   Old: "let $S^*$ be the set of these $j$ with $k_j=k^*$"
   New: "let $S^*$ be the set of $j$ with $\lambda_j=\lambda_F$ and $k_j=k^*$"
   Reason: "these $j$" had no clear antecedent. The definition now states both conditions.

Checked and left unchanged: the 4-cycle numbers (exit rates, switch values 1, 2, 1+sqrt2), Lemma upper and (eq:upper-field), Theorem first (i) to (iv) and proofs, Theorem hull (a) to (c) and proofs, p_F and K^red powers, Corollary reducible-crossing and the b_{FG} formula, Example threecycle values (b>2 makes A_2=b valid), and the descriptions of all 9 scripts (counts, thresholds 0.62 and factor 2.5, 5.1820, 3.4179, 0.438, 0.545, S from 4 to 32, N=40000, 10^-3, 0.05%).
