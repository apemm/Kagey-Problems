# Exhaustive middle-cell formulas for fixed orders

Research note, 8 November 2026. This supplies an exact finite checker for the middle-cell reduction.
It does not assume the report's classification of geometric obstructions. The boards here are pure
`1, x, h` cores, trimmed to their first and last double. They have width `4q-3`, with no collar.

## 1. A complete construction from rectangle differences

Fix the order of the doubles. Each middle cell has a Boolean variable: false means row 1 and true
means row h. Every other cell has a fixed color. For two distinct rectangles R and T, their
presentations coincide exactly when every cell of the symmetric difference `C(R) Δ C(T)` is black.
Consequently:

1. If any cell of the symmetric difference is constantly white, this pair never collides.
2. If two cells demand opposite values of the same middle variable, this pair never collides.
3. Otherwise the pair forbids exactly the conjunction of the middle-variable values required by
   its symmetric difference. An empty conjunction means that the order is invalid for every assignment.

This proves soundness of each generated clause without relying on a list of right-angle or
Pythagorean cases. To prove completeness, three common visible corners determine a rectangle,
so a collision can show at most two points. Enumerate every rectangle, and every possible coloring
of its middle-column corners. Store its possible presentations of size at most two. Any actual
colliding pair occurs in a common bucket. Comparing all pairs in those buckets and applying the
symmetric-difference rule therefore finds every constraint.

The shared corners' colors must not be imposed as part of the constraint. The difference-set
identity already gives equality of the presentations regardless of those shared colors. Dropping
such unnecessary conditions also avoids adding spurious variables to a clause.

This procedure yields an exact CNF at every height. Proposition 17 predicts that in the pure family
with h congruent to 3 modulo 4 its raw clauses use at most two variables. The implementation checks
that conclusion instead of assuming it. The implication-graph test is linear in the generated
formula size; generating the complete formula is a separate, larger computation.

## 2. Exact finite results

| Order | Width | Rectangles enumerated | Unit clauses | Binary clauses | Valid middle assignments |
|---|---:|---:|---:|---:|---:|
| Seven-row order in REPORT.md | 45 | 24,205 | 1 | 6 | 128 |
| Eleven-row order `dfs_gap_h11_s23.json` | 117 | 435,307 | 5 | 33 | 384 |

The original seven- and eleven-row witnesses have one additional sea column at each end.
These computations concern their trimmed cores. They do not show that every assignment listed
here extends to either original end configuration or to a collar.

For seven rows, all 2^11=2,048 assignments were compared with direct presentation equality on an
independent rectangle enumeration. There were no discrepancies. For eleven rows, the independent
enumeration agrees on all 435,307 rectangles; 32 random assignments and the returned satisfying
assignment were checked against direct presentation equality.

The eleven-row count 384 was also checked independently by exhaustive truth tables on the
connected components of the formula. The largest component has 11 variables. The nontrivial
component counts multiply to `2^7 * 3 = 384`; all other components have one assignment. Thus the
count is exact, rather than an estimate from sampled middle-cell choices.

Random orders at heights 7 and 15 also produced only constant, unit, and binary constraints.
Both orders had an empty clause. The height-15 run enumerated 2,961,801 rectangles and produced
three unit and 172 binary constraints in addition to the empty clause. These failures concern
those particular orders and say nothing about all orders at those heights.

## 3. Reproduction and evidence

All scripts use the Python standard library. From this directory, run:

```text
python exact_middle_clauses.py --input order_h7.json --exhaustive --output middle_valid_h7.json
python exact_middle_clauses.py --input ../2026-11-07/data/dfs_gap_h11_s23.json --verify 32 --output middle_valid_h11.json
python exact_middle_clauses.py --input ../2026-11-07/data/dfs_gap_h11_s23.json --output middle_count_h11.json
python check_middle_count.py
```

The first rectangle enumeration uses perpendicular integer side vectors. The independent
enumeration uses equal-length diagonals with a common midpoint. `middle_count_h11.json` includes
an explicit rectangle-pair certificate for every clause. In a forbidden conjunction, signed
variable `+v` requires middle gap `v-1` to be h, and `-v` requires it to be 1. The corresponding
logical clause negates those requirements.

The compiler is a finite research checker, not an efficient general-height order search. Its
exhaustive geometry enumeration grows quickly, and the recursive SCC and model-count routines
are intended for the moderate heights studied here.
