# Paper C and F plan review, October 23, 2026

Scripts behind Section 8 of `reports/Paper C and F plan review - 2026-10-23.md`.
All use the zeta-type run law f(n) = n^(-alpha-1)/zeta(alpha+1), alpha = 1.5, fresh plus start,
and the exact occupation law by the run recursion in double precision. Run with `py -I <script>`
from this folder (slope_check.py, coeff_check.py and antimode_refined.py exec the definitions in
atlas_check.py).

- atlas_check.py N1 N2 ...: boundary layer, antimode and big-jump ratios (reproduces the plan's numbers).
- slope_check.py: the junction excess [P_N(N-j)/T(N) - u(j)] N/j against the plan's coefficient.
- coeff_check.py: the exact fixed-j coefficient C(j) against the finite-N excess up to N = 4800.
- antimode_refined.py: antimode predicted by argmin_j [u(j) + C(j)/N] against the plan's law and the data.
- cut_transpose.py: a 4-state generator with a rank-one cut whose cut-transpose normalizes to a third
  generator with the same principal minors (hence the same Donsker-Varadhan functional).
- outputs_2026-10-23.md: recorded outputs.
