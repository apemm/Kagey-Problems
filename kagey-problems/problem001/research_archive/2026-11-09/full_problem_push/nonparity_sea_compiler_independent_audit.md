# Audit of the full nonparity sea compiler at height seven

9 November 2026. The compiler path for the partition
`{1,3,6} | {2,4,5,7}` passes independent review. The full exported residual
model was regenerated exactly, and its periodic acceptance agrees with an
independent geometric test on all words of periods one through four.

## Exact partition-dependent conditions

The row partition enters `forbidden_patterns` through the predicate that two
rows lie in different blocks. This predicate appears precisely in the
singleton and vertical-white-pair axis-rival tests. Those are the two cases
requiring an edge of the final complete bipartite row graph. Horizontal and
oblique rivals use black points in their shown columns and do not depend on
the partition. Hidden tilted rectangles and tilted/tilted symmetric
differences are likewise partition independent.

Normalization rejects only supports requiring two different black rows in
one sea column. It may move the black support away from a common white corner
outside a finite prefix, which can prune prefixes without bi-infinite
extensions. This does not change the bi-infinite sea shift or its recurrent
components. Inclusion reduction removes only a pattern containing a translated
smaller positive forbidden pattern.

The residual exporter then depends only on these exact positive patterns.
Its subset/superset merging, wildcard shift, and native packed-state handling
have the same semantics as in the previously audited parity model. No
parity-specific assumption occurs in those operations.

## Full input and independent periodic checks

The saved input `sea_residuals_h7_p136.json` has partition `[1,3,6]`, 85 tilted
shapes, 3,151 minimal patterns, maximum pattern span 20, and 7,950 residuals.
It has no truncation flag. Regenerating the complete export gives identical
JSON and the identical SHA-256 digest:

```
a69b92322fb819b58889449fa3d27fc35fc0e36bc94cf8f5a314f8752df89106
```

`verify_nonparity_sea_periods.py` independently generates rectangles from
equal-length diagonals with a common midpoint. It compares their actual white
presentations and applies the explicit final-row-graph axis-rival tests. For
a period of length p it checks p+20 columns. This length contains every
horizontal phase of every possible tilted comparison, including its common
white corners, and therefore resolves the finite-boundary normalization issue.

The independent geometric result agrees with the residual automaton on every
one of the 2,800 words of periods one through four, separately for both the
ordinary parity partition and the partition `{1,3,6}`. Accepted word counts
are as follows; words of smaller fundamental period are included.

| Tested period | Ordinary parity | Partition `{1,3,6}` |
|---:|---:|---:|
| 1 | 7 | 4 |
| 2 | 45 | 16 |
| 3 | 205 | 124 |
| 4 | 1081 | 208 |

The saved result is `nonparity_sea_periodic_audit.json`. These short-period
counts are calibration checks, not an estimate or comparison of the two
entropies. A spectral comparison requires the separate exact integer
certificates on the complete graphs. This audit finds no compiler or
partition-semantics issue that would invalidate that comparison.

## Complete partition comparison and counting consequence

`certify_height_seven_partitions.py` also passes independent code review. It
enumerates every size-three row block, quotients only by physical vertical
reflection, and obtains 19 classes whose orbit sizes total 35. Each selected
export identifies its row partition, up to exchanging the two blocks. The
three full models are distinguished from the sixteen models retaining only
patterns of span at most ten.

Deleting true forbidden patterns enlarges the accepted shift. Consequently
each truncated model gives an upper bound for its original partition's
entropy, even when the two models have different state counts or components.
The script verifies the complete SCC decomposition and integer Collatz
bounds, then compares exact integer cross-products. Floating-point values
are not used to certify the winner.

The completed comparison has the unique maximizing reflection class
`{1,3,6}`, with its reflected class `{2,5,7}`. Its certified radius lies in
`[3.780928,3.780929]`. The nearest competitor `{1,4,6}` lies in
`[3.776961,3.776962]`, and ordinary parity lies in
`[3.776799,3.776801]`. The other sixteen upper models lie strictly below the
winning lower bound. Thus ordinary parity does not maximize the sea entropy
at height seven.

The full winning graph has one recurrent component and contains the row-1
self-loop, so its dominant component is primitive. In the established
end-aware equality transfer, all other sea states are transient or have
smaller exponential growth. The closed insertion bridge for each of the
twelve final row pairs gives a positive critical insertion factor. The
dominant pole therefore has order thirteen, giving

\[
a_7(m)\sim C_7 m^{12}R_7^m,\qquad C_7>0.
\]

Here `R_7` is the spectral radius of the full winning component. Vertical
reflection is a bijection between the two winning labeled-partition families,
so their leading constants agree and `C_7=2 C_{136}`. The constant must use
the end-aware initial and final weights and insertion factors. Replacing them
by the raw sparse automaton's empty initial state and all-accepting terminal
vector would ignore the finite-boundary qualification discussed above.
