# Problem 137, general version

Paper: `problem137_general.pdf`, "Why three? Trees of rationals from x -> x + 1 and an involution",
written for the Journal of Integer Sequences. It explains the 3 in a(n) = a(n-1) + a(n-3) as the order
of g o f, by replacing g(x) = -1/x with g_m(x) = -1/(mx).

## Results and their status

| statement | status |
|---|---|
| Theorem A_q: rank g.f. N_q/D_q, D_q = 1 - t - t^3 - ... - t^{2q-3}, recurrence from n = 2q - 2, fails at 2q - 3 | proved, every q >= 3 |
| Theorem B_q: run rule (no q - 2 interior 1's in a row), unique reduced word, rank = c_1 + ... + c_k + k - 1 | proved, every q >= 3 |
| Theorem C_q: parent map gives shortest paths, blue iff negative, children, jump of 2q - 3 ranks | proved, every q >= 3 |
| Theorem D: m = 1, 2, 3 trees contain every rational | proved |
| Theorem E: m >= 4 gives Fibonacci counts, -1 and 1/2 never reached | proved |
| Proposition 6.2: psi_q Pisot, C_q, blue share 1/(1 + psi_q), psi_q increases to the golden ratio | proved |
| a_q(n) = nearest integer to C_q psi_q^n | computer-checked for 1 <= n <= 80, q = 3, 4, 5, 6 (40-digit floats) |
| tree = lambda_q Q(lambda_q^2) for q = 5, 8, 10, 12 | from Leutbecher (1974, Satz 2) plus Proposition 3.4(d) |
| other involutions (ax + b)/(cx - a) | open question |

q = 3, 4, 6 correspond to m = 1, 2, 3. q = 3 is the earlier paper `../problem137.tex`.

## Files

- `problem137_general.tex` main file, with sections `sec_intro.tex`, `sec_parent.tex` (setting,
  parent map, reachability), `sec_words.tex` (run rule), `sec_count.tex` (counting and growth),
  `sec_free.tex` (m >= 4), `sec_final.tex` (computations, related work, open questions), `bib.tex`.
- `figures/` holds `fig_tree_m1.tex`, `fig_tree_m2.tex` (TikZ) and `growth.pdf`, all made by
  `make_figures.py`.
- `verify_general.py` recomputes every number in the paper by two methods (BFS in exact arithmetic,
  and enumeration of reduced strings; also the parent map and a symbolic transfer matrix). It takes
  about five minutes and prints `ALL CHECKS PASSED`. Needs `sympy` and `mpmath`.
- `data/` is the working record: `ledger.md` (predictions before each computation, outcomes after),
  `checks_report.md`, `literature.md` (what was read and at what access level), the proof files
  `proofs_route1.md`, `proofs_route2.md`, `proofs_final.md`, and raw run outputs.
- `explore.py`, `words.py`, `q5.py`, `route2_checks.py`, `route2_asymp.py` are the exploration
  scripts behind the ledger. The paper relies only on `verify_general.py`.

## Build

```
pdflatex problem137_general.tex   (three times)
python make_figures.py            (only to redraw the figures)
python verify_general.py
```

## Before submission

- Fill in the bracketed placeholder in "A note on the use of AI" (how the proofs were checked).
- Sources read only second-hand (Rosen 1954, Hecke 1936 via its JFM review, Leutbecher 1974 beyond the
  introduction) are cited only for attribution. See `data/literature.md`.
