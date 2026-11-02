# Paper D verification audit

This audit checks the executable evidence and the stated scope of the Lean
formalization. It does not treat a successful program run as a substitute for
the mathematical arguments in the paper.

All checks completed successfully. The six-script quick suite passed, including
the three fresh threshold probes. The final revised modes script passed
separately. The Lean audit checked all 308 modules and 23,503 declarations,
found no unimported files, and reported only `propext`, `Classical.choice`, and
`Quot.sound`. Its 13 build warnings concern linting or deprecations. Direct
source re-elaboration of `ShapeAllEven.lean` also passed.

## Changes

- The verification section now refers to Section S5 from the combined arXiv
  build and to the arXiv version from the journal build.
- It separates kernel checking from checking that the formal statements match
  the manuscript. The kernel check is independent of who wrote the proof terms.
- It states that the new analytic-density lemma, strict monotonicity,
  uniqueness of modal points, inflection-point classification, fourth-moment
  extension to `a >= 4/5`, and sharper Jensen center bound have not been formalized.
  The existing Lean result proves the non-strict monotonicity dichotomy and
  excludes unimodality in its second case.
- The illustrative bisection in `verify_elephant_modes.py` no longer claims
  that its midpoint lies inside the much narrower certified threshold interval.
  It checks five-decimal agreement and separately checks, with exact rational
  comparisons, that its coarse bracket contains the certified interval.
- The modes script checks the new fourth-moment beta factor at six rational
  arguments. It also checks the derivative numerator by exact polynomial
  coefficient arithmetic, and the rational bound `141/80 < 9/5`. The old
  `a >= 39/40` calculation is labelled as a historical proof check.

## Formal correspondence checked

`PaperD/ShapeAllEven.lean` states the full all-even crossing result with the
single size assumption `4 <= h`, where the walk has `2*h` steps. Its conclusion
includes the strict interior minimum at the center, positive central second
difference, and the complete pair of intervals of global maximizers. The
definition of the crossing and the endpoint certificates enter through imported
proved results, rather than through an added asymptotic hypothesis.

`PaperD/Modes/TwoModes.lean` assumes the named density and law-convergence
hypotheses. Its `two_modes` theorem concludes non-strict monotonicity on the
appropriate intervals. `main_limit_near_one`, for the former `a >= 39/40`
range, additionally uses the cited moment
formulas and the identification of the absolute-value distribution with its
density integral. These hypotheses are not removed by an axiom check: a theorem
of the form `H -> conclusion` can use only standard logical axioms while still
requiring `H`.

The composed bulk results in `PaperD/U_EndToEnd.lean` retain named classical
inputs. In particular, its compound-Poisson bound is pointwise. It does not
formalize the later total-variation strengthening. This distinction was already
present in the manuscript and has been retained.

## Reproduction and records

The Python runs use a separate copy of the scripts and data so that they do not
overwrite the original archived outputs. `runtime.json` gives the versions used
for this audit. The archived October certificate runs used a different Python
and python-flint version; their provenance is left intact.

The normal commands, from `kagey-problems/problem131/paperD`, are:

```text
python -B verify_all.py --quick
python -B verify_elephant_modes.py
```

The second command verifies the revised bisection check. The audit's six-script
run used the preceding version of that one illustrative script; all five other
scripts and the four threshold-certificate source files are unchanged.

The Lean commands use Lean 4.33.1 and the existing workspace outside OneDrive:

```text
lake build PaperD
python -B verify_lean.py PaperD --workspace C:/Users/arjun/lean-work/paperD
```

The audit redirects the verifier's output constants to this directory, preserving
the repository's October manifest. The build uses existing cached dependencies
and proof objects. A direct source re-elaboration of `ShapeAllEven.lean` provides
an additional check of that composed theorem; this is not a from-scratch rebuild
of all 308 modules.

## Scope limits

- The audit does not rerun the nine full threshold-certificate jobs or the full
  range of the separate center and convexity certification scripts.
- The quick threshold run checks source hashes, the signs and coverage of the
  stored intervals, and three freshly computed probes. These are different
  checks from recomputing the entire certificate.
- The analyticity lemma and its shape consequences, sharper center bound,
  fourth-moment extension, total-variation strengthening, enlarged weak-Landau
  range, fixed-memory bridge, likelihood theorem, and threshold certificate
  remain outside the Lean
  formalization. No new Lean proof has been added in this revision.
- Only the named composed results and the formalization's interfaces were read
  directly for correspondence. The 23,503 declarations have not each received a
  separate manual proof audit.

Final execution results are recorded in `results.json` and the adjacent logs.
