# Independent audit of the exact width-14 multiplicity

9 November 2026. The complete enumeration establishes
\[
 a_7(14)=80,
\]
with the existing exact-solver trust qualification. Each board has \(24\) black cells.

The axis-valid classification at excess ten leaves four families:

| Family | Vertical-reflection classes |
|---|---:|
| Ten double columns, no empty column | 1,497 |
| One triple and eight doubles, no empty column | 957 |
| Eleven doubles and one empty column | 210 |
| Twelve doubles and two empty columns | 19 |

The first three families are the existing \(2,664\)-core catalog. The fourth family is necessary at width fourteen and was checked separately; it must not be omitted merely because it did not fit the earlier width-twelve/thirteen catalog.

The independent verifier regenerates all ten-edge triangle-free graphs on seven rows. It also regenerates the triple family from the equality structure: choose the triple, choose a \(K_{2,2}\) on the four outside rows, and attach each outside row to one triple row, with adjacent outside rows receiving different attachments. This gives \(1,890\) raw triple cores and \(957\) reflection classes. The eleven- and twelve-double families come from all balanced \(K_{3,4}\) graphs, with respectively one edge removed or none. The regenerated ordered catalog agrees exactly with the solver's catalog.

Both primary shards have all \(1,332\) assigned cores complete, for a disjoint total of \(2,664\). Their weighted counts are \(24\) and \(56\). The separate two-empty run has all nineteen cores complete with zero models. There are no unresolved, timed-out, or model-capped records in this combined count.

The projected blocking clauses are exact because every encoded board has the same black count. The once-only smallest core mask is anchored in columns one through seven. At even width this selects exactly one board from each horizontal-reflection pair, so every projected model has horizontal weight two. Vertically asymmetric row cores have weight two; self-reflected cores have weight one because their reflected boards are already enumerated. The \(22\) projected models expand to exactly \(80\) distinct boards, agreeing with the weighted total.

[verify_seven_optimum_count14.py](verify_seven_optimum_count14.py) independently constructs rectangles using equal-length diagonal pairs with a shared midpoint. Every one of the \(80\) reflected boards has \(2,691\) distinct presentations. The checker also verifies the black counts, core multiplicities, empty-column counts, anchors, crop bounds, complete record coverage, and source hashes.

The complete boards and certificate are in [seven_optimum_count14_independent_check.json](seven_optimum_count14_independent_check.json). The presentation checks independently prove all eighty boards valid. Exclusion of additional boards relies on the completed projected SAT enumerations and the previously audited exact encoder.
