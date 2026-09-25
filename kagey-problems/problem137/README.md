# Problem 137: the rational tree of x+1 and -1/x (complete solution)

Source: https://peterkagey.com/problems/137/

Starting from 0 and applying f(x) = x+1 and g(x) = -1/x produces every rational number. Let a(n) be
the number of rationals first reached in exactly n steps. Kagey asks whether a(n) = a(n-1) + a(n-3)
for n >= 4, whether the vertices reached last by g are exactly the negative rationals, and whether
the rank-n rationals can be characterized. All 3 are answered in the paper.

Files:
- problem137.tex / problem137.pdf: the paper
- fig_tree.tex: the tree figure (ranks 0 to 7)
- solution.md: the same solution as plain notes
- verify.py: BFS verification through rank 41, reproduces Table 1

Run `python verify.py` (about 35 s, roughly 2 GB of memory at rank 41; lower MAX at the top of the
file for a quicker run).
