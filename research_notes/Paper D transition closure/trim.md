# Prose-only cuts in the crossing and shape sections

Two passes removed **607 whitespace-delimited words** from the two assigned
files. The first pass removed 363 words:

| File | Before | After | Removed |
| --- | ---: | ---: | ---: |
| `sec_erw_crossing.tex` | 2,189 | 2,054 | 135 |
| `sec_erw_shape.tex` | 4,511 | 4,283 | 228 |

The cuts remove repeated roadmaps and shorten explanations of the first flip,
the conditional unimodality citation, the compound Poisson/Landau relation and
the sign recurrence. The prior-work distinctions, numerical examples and
unique mathematical claims remain.

The edit script verified exact preservation of **72 protected blocks**:
definitions, theorems, lemmas, propositions, corollaries, proofs, remarks,
figures, tables, equation environments and display-math blocks. It also
verified that every distinct inline formula in each source is still present.
The recorded counts and normalized UTF-8 hashes are in `trim_output.json`.

`trim_redundancy.py` records this one-time edit against the preceding source.
It is not a manuscript generator and should not be rerun against a later
revision. No Lean file, epigraph or disclosure was changed by this edit.

The second pass removed another **244 words**:

| File | Before second pass | After second pass | Removed |
| --- | ---: | ---: | ---: |
| `sec_erw_crossing.tex` | 2,054 | 2,007 | 47 |
| `sec_erw_shape.tex` | 4,283 | 4,086 | 197 |

This pass condensed the first-order urn comparison, the crossing proof
summary, the first-flip interpretation, and the explanatory summaries of
total variation, convexity and the height window. It retained every unique
mathematical claim, numerical example and citation. No formal proof or
statement was edited.

The second script again verified exact preservation of all 72 protected
blocks and retention of every distinct inline formula. Its counts and
normalized UTF-8 hashes are recorded in `trim_second_output.json`;
`trim_redundancy_second.py` records the one-time edit. Neither pass modified
`app_modes.tex`, `app_bias_interval.tex`, any Lean file, the epigraph or the
disclosure.

Across both passes, `sec_erw_crossing.tex` went from 2,189 to 2,007 words
(182 removed), and `sec_erw_shape.tex` went from 4,511 to 4,086 words
(425 removed).
