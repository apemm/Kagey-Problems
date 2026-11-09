# Independent audit of the seven-row equality count at width 21

9 November 2026. The completed enumeration establishes
\[
 a_7(21)=4,
\]
with the existing exact-solver trust qualification. Every one of the four boards has \(33\) black cells.

The equality classification is complete here: every column is nonempty with one or two black cells, and the twelve double columns realize all edges of one balanced \(K_{3,4}\), each exactly once. Independently enumerating its three-row side gives \(35\) row cores and \(19\) classes under vertical reflection. These agree exactly with the runner's catalog. The result file has one completed record for every index \(0,\ldots,18\), with no missing, timed-out, or model-capped record.

The source [count_seven_equality_optima.py](count_seven_equality_optima.py) uses the previously audited exact fixed-core encoder, all seven singleton types, no empty type, and only established cropped-subboard bounds. Its projection blocker contains the negatives of the \(33\) black-cell variables. Because every encoded board has exactly \(33\) black cells, it excludes exactly that board projection, regardless of auxiliary-variable assignments.

The horizontal anchor is the once-only smallest row-pair mask. At odd width, a model with its anchor strictly left of the middle represents its two horizontal reflections; a middle-anchor model receives weight one because both reflected boards remain in the enumerated half. A vertically asymmetric row core receives weight two. A self-reflected core receives weight one because the enumeration already includes all its vertically reflected boards. These rules remain valid when horizontal and vertical reflections interact.

Only core \(12\), the ordinary parity core, has models. Its two projected models both have their anchor at column \(9\), so each receives horizontal weight two and vertical weight one. Their combined reflection orbit contains exactly four distinct boards.

The independent checker [verify_seven_equality_count21.py](verify_seven_equality_count21.py) imports no rectangle generator or solver encoder. It constructs every rectangle as two equal-length diagonals with a common midpoint. For each of the four reflected boards, all \(5,785\) rectangle presentations are distinct, and none is empty. It also checks the black counts, row cores, symmetry weights, cropped bounds, and catalog coverage.

The certificate, complete column words, and source hashes are saved in [seven_equality_count21_independent_check.json](seven_equality_count21_independent_check.json). The presentation checks independently prove validity of all four boards; the exclusion of additional boards relies on the completed projected SAT enumeration.
