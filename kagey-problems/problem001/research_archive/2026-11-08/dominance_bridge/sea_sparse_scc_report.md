# Exact compressed sea graphs at heights five and six

Research note, 8 November 2026. This computation settles dominance of the constant-state component
within the parity sea shift at heights five and six. It does not compare parity with other row
partitions at those heights. The larger-height runs recorded below are explicitly incomplete.

The separate follow-up `partition_dominance_h5_h6.md` uses the same engine for all 20 balanced
partitions at heights five and six. It certifies strict parity dominance at both heights and records
independent exhaustive periodic checks. The present note supplies the compressed-engine proof and
the within-parity SCC certificates on which that follow-up builds.

## 1. Certified results

The exact sparse automaton has the following structure. These are compressed automaton state
counts, not full length-2W window counts.

| Height | Reachable compressed states | Labelled edges | Unique cyclic SCC | Transient singleton SCCs |
|---|---:|---:|---:|---:|
| 4 | 59 | 186 | 52 | 7 |
| 5 | 1,600 | 5,325 | 1,436 | 164 |
| 6 | 67,689 | 242,120 | 65,414 | 2,275 |

At each of these heights the unique cyclic component contains every constant-row state. It has
self-loops and therefore period one. Every other SCC is a transient singleton. Thus the component
C_* containing the constants is the unique maximal-entropy component, and indeed the only cyclic
component, of the parity sea shift at h=4,5,6.

The h=4 full-window graph has 2,368 states in one SCC, as separately computed in
`../counting_followup/dominance_h4_verification.json`. The h=5 full-window graph in the earlier
report has 1,066,807 states. Neither number should be confused with the compressed counts here.

Exact rational Collatz certificates give, with conservative outward decimal rounding,

    3.54387564628 < rho_5 < 3.54387564630,
    3.5896958401  < rho_6 < 3.5896958405.

The exact rational endpoints are in `sea_sparse_h5.json` and `sea_sparse_h6.json`. The latter
replaces the earlier Monte Carlo estimate by a rigorous enclosure for the full parity sea shift.

## 2. Exact forbidden patterns from geometry

A positive pattern specifies black rows at a finite set of columns. It occurs when every specified
cell is black; all intervening columns are unrestricted. If two specified cells have different rows
in the same column, the pattern is impossible in a sea and is discarded.

The generator enumerates every tilted rectangle, up to horizontal translation, by side vectors
(a,-b),(c,d), with positive a,b,c,d, ac=bd, and total vertical span b+d<h. It adds the following
positive forbidden patterns.

1. All four corners of a hidden tilted rectangle.
2. Three corners plus a black cell of opposite row parity in the fourth corner's column. The
   resulting singleton presentation has an axis rival through the parity pair set.
3. For a vertical white pair of opposite row parity, the other two black corners. This remains
   fatal if one cell of the proposed white pair is black: the same axis rectangle then gives
   a singleton rival. Both cells cannot be black in one sea column.
4. For a horizontal white pair, the other two corners and a common black row in the two white
   columns, different from their white row.
5. For an oblique white pair, the other two corners and the two crossed black cells.
6. The symmetric difference of any two tilted rectangles sharing a corner. A pair sharing two
   corners contributes four black cells; a pair sharing one contributes six. Distinct rectangles
   cannot share three corners. Pairs sharing no corners would require two hidden rectangles,
   already excluded by item 1.

Hidden rejection is sound for every sea. For completeness, a hidden rectangle with an oblique
diagonal A,C gives two colliding rectangles by adjoining the crossed cells (A_x,C_y),(C_x,A_y)
to its two diagonal pairs. If neither diagonal is oblique, the tilted rectangle is a 45-degree
diamond with two black points in one column, impossible in a sea.

For tilted pairs, the implementation anchors a common corner at column zero and compares every
pair of incident rectangles. This enumerates every nonempty intersection up to translation.
The presentation difference identity makes item 6 exact without any white-cell hypotheses.
The axis-rival lemma gives completeness of items 2 to 5. Hence the forbidden patterns recognize
exactly the bi-infinite parity sea shift.

There is an important finite-boundary distinction. Patterns are normalized by their black support.
A common white corner of two rectangles can lie outside that support. The automaton can therefore
reject a finite word that passes the rectangle-contained finite checker, but only when that word
has no bi-infinite extension. For example the six-row word

    (1,1,6,1,4,6,4)

passes the finite checker. Prepending any one of the six rows makes it invalid. Before normalizing,
the responsible rectangles share (0,3) and have complementary black triples

    {(1,1),(6,6),(7,4)},  {(2,1),(3,6),(5,4)}.

The common corner is one column left of the normalized word. This boundary pruning does not change
the sea shift, its recurrent SCCs, or its entropy. No claim of equality with every finite
rectangle-contained prefix language is made.

The generator removes a pattern whenever it contains a translated smaller forbidden pattern.
This is logical subsumption, so it preserves the language. Pattern statistics are:

| Height | Minimal patterns | Patterns with 2, 4, 6 cells | Maximum span | Distinct residuals |
|---|---:|---|---:|---:|
| 4 | 52 | 0, 44, 8 | 6 | 72 |
| 5 | 288 | 0, 206, 82 | 10 | 454 |
| 6 | 1,084 | 2, 576, 506 | 14 | 2,256 |
| 7 | 3,230 | 4, 1,292, 1,934 | 20 | 8,160 |
| 8 | 9,754 | 6, 2,768, 6,980 | 26 | 29,702 |

## 3. Why the compressed automaton is exact

After reading a prefix, a live residual records the future cells still required to complete some
forbidden pattern whose already-read requirements matched. Reading a new letter kills residuals
that disagree with it, advances surviving residuals, rejects if any pattern completes, and starts
new pattern occurrences at the new column.

If residual P is a subset of residual Q, every completion of Q also completes P. Thus Q can be
discarded whenever P is live. A state is the antichain of inclusion-minimal residuals. This is an
exact representation of the disjunction of all future forbidden completions. Its derivative under
each new letter is therefore exact. Breadth-first enumeration from the empty prefix constructs
every reachable derivative state and every allowed labelled transition of this pattern language.

The optimized implementation groups residuals with the same normalized future requirements and
different leading wildcard runs. Their time advance is a single bit shift. The shifted wildcard
part remains an antichain; only newly started and just-matched residuals need to be merged into it.
This changes representation and runtime, not the derivative operation.

## 4. Why recurrent SCCs correspond to full-window SCCs

A generic deterministic quotient can merge recurrent components. That issue does not arise here.
Let L be the maximum forbidden-pattern span. After any L legal letters, every residual inherited
from before those letters has expired. Therefore the current antichain state is determined solely
by the last L labels, independently of earlier history or the starting derivative state.

Consequently every bi-infinite labelled path has exactly one compatible antichain-state path.
Reading labels gives a bijection between the bi-infinite labelled automaton presentation and the
sea shift, and the inverse uses only the last L labels. This is a finite-memory conjugacy, not
merely a language-preserving quotient.

One can also see SCC correspondence directly. Map a recurrent full-window state w to its derivative
state. This map is defined on every recurrent window, because a window pruned by a normalized
pattern has no bi-infinite extension and therefore cannot be recurrent.
If two recurrent full-window components mapped into the same derivative component, connect their
images there and then replay L labels ending at a chosen recurrent target window. The lifted path
ends at that target window. Reversing the construction connects back, so the two full-window
components were the same. Conversely, a derivative cycle lifts to a periodic label sequence and
therefore to a full-window recurrent component. Component entropy is preserved by the same
finite-memory correspondence.

Thus the unique cyclic SCC computed at h=5 and h=6 certifies the corresponding structural assertion
for the original sea shift.

## 5. Exact spectral bounds

For each cyclic component, floating-point iteration of M+I proposes a positive vector. Its entries
are converted to positive integers. The program then recomputes Mv with exact integer arithmetic
and evaluates

    min_i (Mv)_i/v_i <= rho(M) <= max_i (Mv)_i/v_i

as exact rational numbers. The floating-point iteration is not used as a certificate: any positive
integer vector gives valid Collatz bounds. Parallel labelled edges are counted with multiplicity.
All other SCCs at h=4,5,6 are acyclic and have spectral radius zero.

## 6. Independent verification

`verify_sea_sparse.py` compares automaton acceptance with the geometric checker on every word in
three finite sets, which agree at the stated lengths:

* 65,536 four-row words of length eight.
* 78,125 five-row words of length seven.
* 7,776 six-row words of length five.

It also checks 1,200 longer legal walks and one-letter mutations. These latter checks are samples,
not exhaustive certificates. Finally it compares the entire tilted-rectangle placement set in a
full collision window with the independent diagonal-based `verify_narrow.rectangles` generator:
26 rectangles at h=4, 138 at h=5, and 480 at h=6. Every comparison passes, including after the
transition optimization. A separate exact test verifies the finite-boundary counterexample in
section 2 and all six of its one-column left extensions. The general shift-level correctness proof
is in sections 2 to 4; short finite-word agreement alone is not that proof.

## 7. Larger-height barriers

The first h=7 run stopped at its 150-second time cap: 66,000 states processed and 229,951 states
discovered. The graph was incomplete. It proves neither uniqueness nor nonuniqueness of recurrent
components.

The optimized h=7 run also stopped at its time cap. It processed 196,000 states and discovered
641,060 states in 482.625 seconds, with reported memory usage 774.64 MiB. Its limits were 480 seconds,
1.5 million discovered states, and 1,200 MiB. The small time overshoot comes from checking the cap
after each batch of 1,000 processed states. The result is stored in `sea_sparse_h7_optimized_cap.json`,
and progress checkpoints are preserved in `sea_sparse_h7_optimized_progress.log`. This attempt
remains incomplete and gives no h=7 SCC or Perron certificate. No further extension was run.

The h=8 probe stopped at its 45-second cap: 1,000 states processed and 7,174 discovered. This graph
was also incomplete and yields no SCC or Perron conclusion. Its large residual universe already
makes the current representation expensive. These partial runs must not be reported as exhaustive
checks of h=7 or h=8.

All files in this note are local research artifacts. No commits were made.

## 8. A further exact compression to try

Antichain subsumption does not use every finite-alphabet identity. For example,

    OR over a=1,...,h of (P AND [X_j=a]) = P.

A reduced ordered h-ary decision diagram for the residual bad-future function would identify such
equivalent disjunctions. A transition restricts X_0 to the new row, shifts the remaining variables,
and takes the union with newly started forbidden patterns. Identical child lists are shared, and a
node whose h children agree is deleted. This is an explicit next implementation step, not a completed
computation.

If reduction makes the bad-future function identically true, the prefix has no infinite extension.
It can be pruned for the sea shift and SCC computation, even if its finite rectangle-contained
prefix is still valid. Thus this optimization needs the same finite-boundary qualification as
section 2. It could substantially reduce the h=7 and h=8 state growth beyond the current antichain
representation.
