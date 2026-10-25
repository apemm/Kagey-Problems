# Lean integration, October 25, 2026

This follows Section 8 of `01_plan.md`, except item 7: `lean/.lake` was kept. The inputs were the
logs `W-C1_log.md`, `W-C2_log.md`, `W-D_log.md`, `W-F_log.md` and `W-S4_log.md`. No git command
that changes state was run.

## 1. Forbidden tokens and sub-roots

`grep -w` for `sorry`, `admit`, `native_decide`, `axiom` and `opaque` over `PaperC/C1`,
`PaperC/C2`, `PaperD/Modes`, `PaperD/S4`, `PaperF/Exact` and their five sub-root files found
nothing. The sub-roots are where Section 8 expects them (`PaperC/C1.lean`, `PaperC/C2.lean`,
`PaperD/Modes.lean`, `PaperD/S4.lean`, `PaperF/Exact.lean`), and each imports every module of
its folder (14, 20, 22, 5 and 11 modules). Every statement label cited in a module docstring
exists in the corresponding paper source.

## 2. Edits to the shared roots and to the new folders

- `lean/PaperC.lean`: `import PaperC.C1`, `import PaperC.C2`.
- `lean/PaperD.lean`: `import PaperD.Modes`, `import PaperD.S4`.
- `lean/PaperF.lean`: `import PaperF.Exact` (the file keeps its CRLF line endings).
- No name clashes: every library built at the first attempt that had enough memory.
- `verify_lean.py` refuses private theorems ("make it public"). Five private helper theorems in
  `C1/` were made public, with no change of name or statement: `lRev_eq`, `uRev_pos`
  (`CriticalPoint`), `s2`, `s6` (`CubicCycle`), `prod_sqrt` (`SymFace`). The three modules were
  rebuilt.

## 3. Builds (original workspaces, one library at a time)

Before the roots were edited, `lake build PaperC --no-build` and `lake build PaperD --no-build`
reported every target up to date (8726 and 8985 jobs). In `PaperF`, `Green` and `Inverse` were
stale (their sources were edited on October 24 after the last build) and were rebuilt.

- **PaperC.** The first `lake build PaperC` failed: 15 new modules compiled in parallel and
  Lean stopped with `INTERNAL PANIC: out of memory` and failures to read Mathlib `.olean` files.
  This was a resource failure, not a source error. Building the new modules one per `lake build`
  call worked (all 34 exit 0), and then `lake build PaperC` completed (8762 jobs).
- **PaperF.** Built module by module, then `lake build PaperF`: exit 0 (8726 jobs). There are
  linter warnings in `Exact/` (unused variables and simp arguments, `<;>`), no errors.
- **PaperD.** Built module by module with a check that stops on any `T7_Gen_*` rebuild: all 29
  new modules and sub-roots exit 0, and only they were compiled. No old module was rebuilt.

`python -B verify_lean.py PaperC PaperD` (default workspaces) passed in 6 min 47 s and rewrote
`build-log.txt` and `verification-manifest.json`: "All checks passed: PaperC, PaperD (24218
declarations)". `PaperD` was replayed apart from the root, with 13 replayed linter or
deprecation warnings. `verify_lean.py` was not edited.

## 4. Counts and axioms

| Library | Modules | `theorem`/`lemma` declarations | New modules (with sub-root) | New declarations |
|---|---|---|---|---|
| PaperC | 56 (was 20) | 715 (was 409) | C1: 15, C2: 21 | C1: 150, C2: 156 |
| PaperD | 308 (was 279) | 23503 (was 23261) | Modes: 23, S4: 6 | Modes: 159, S4: 83 |
| PaperF | 20 (was 8) | 252 (was 107) | Exact: 12 | 145 |

The counts are those of `verify_lean.py`'s parser (for PaperF obtained by calling its functions,
without editing it). Axioms: for PaperC and PaperD, `verify_lean.py` reports every declaration
within `propext`, `Classical.choice`, `Quot.sound`. For PaperF the scratch file
`~/lean-work/paperF/AxiomsAll.lean` imports `PaperF` and runs `collectAxioms` on every theorem of
the 18 modules that declare anything: 344 theorems (708 with the auxiliary ones Lean generates),
no axiom outside the three, no `sorryAx`.

## 5. Statement fidelity (3 headline theorems per paper)

Each Lean statement was read against the paper statement by label. "Listed" means the log
already records the deviation; "unlisted" items are new here. No theorem was changed. All of this
is in the MAP rows.

**C1.**
- `lem:weighted-cayley` / `weighted_cayley_det`: the tree sum is the determinant of the reduced
  Laplacian (no matrix-tree theorem in Mathlib); states `Fin (k+1)`, Lean's `k ≥ 1`. `x > 0` as
  in the paper. Listed.
- `prop:discrete-rate`(a) / `dvRateH_restriction`: `Q` Metzler, `h > 0`, `1 + hQ_ii > 0`, `α ≥ 0`
  zero off `F`. These generalize the paper (no sum one, a weaker condition on `h`). Listed.
- `lem:admissible` / `admissible_iff_walk`, `admissible_iff_components`: adds `μ ≥ 0`, `a ≥ 0`,
  `h > 0`, `hq_i < 1`, which are the model's standing assumptions stated explicitly. Listed. No
  unlisted deviation found.

**C2.**
- `thm:memoryless` / `memoryless_*`, `lawP_aBlock`: `Memoryless` is weaker than `def:memoryless`
  (`B` nonempty, no sign on `κ`, `c`). Unlisted: the transform identity `F_{Q^[B]} = F_Q` is not
  stated as such. Lean has the equality of the count laws of `I + hQ` and `I + hQ^[B]` for every
  `N` and `h`, which is the discrete statement of the theorem.
- `thm:nonreversible`(c) / `pminor_cutTranspose`: no hypotheses at all. Unlisted: only the
  invariance of the minors under one cut-transpose is proved, not that the fiber is the set of
  generator points of the orbit or the `2d` bound.
- `rem:stationary` / `lawP_aRev`: any positive `π`; stationarity only for `aRev_exit`. Listed.

**D.**
- `thm:two-modes` / `two_modes`: named hypotheses `DensityHyp` (continuous, even, nonnegative,
  integrable, **bounded**) and `LawConvHyp`. Listed, but the log attributes all of `DensityHyp`
  to Guérin, Laulin and Raschel, Theorem 1.3. Unlisted: boundedness is an addition for the proof,
  and the theorem's last sentences (strict local maxima only at `0`, resp. `±c`, and the case of
  no constant interval) are not formalized. The Taylor constant `2M₄η⁴` (for `M₄η⁴/12`) is listed.
- `cor:height-window` / `height_window`: the rise, plateau and fall of `P_N` on `[l, r]` are
  hypotheses (the conclusion of `modal_intervals_at_crossing_all_even`). Listed.
- `thm:two-modes-near-one` / `main_limit_near_one`: adds `GLRMomentsHyp`, `X ∈ L²` and
  `P(|X| ≤ t) = 2∫_0^t g`, plus `DensityHyp`, `LawConvHyp`. Listed. Unlisted, minor:
  `near_one_not_concave` assumes `P(|X| ≤ 0) = 0`.

**F.**
- `eq:cover` / `cover`: only `f σ 0 = 0`. No deviation.
- `lem:counting`, second part / `counting_two_long`: the event counts run lengths inside the
  first `N` slots, which is a smaller event than the paper's (full lengths). So the Lean bound is
  **weaker than the paper's statement**, and the paper's event is not covered. Listed in the log,
  but only as a choice of form; the MAP now says plainly that the paper's bound is not in Lean.
- `cor:four-modes` / `four_modes_core`: adds `u ≥ 0` (listed). Also takes the strict decrease of
  `u` on `j ≥ 1`, `u(1) < 1`, `u → L`, `L < u(d₀)` as hypotheses (the output of
  `lem:logconvex`). The conclusion "at least four modes for all large `N`" is not formalized
  (implicit in "core").
- (also read) `lem:logconvex` / `logconvex_lemma`: the renewal theorem is a hypothesis. Listed.

**Coin-turning note.**
- `thm:aging-d` / `thm_aging_d_a`, `thm_aging_d_b`, `thm_aging_d_corner`: indexing by `N - 1`,
  count vectors with first part at least 1. Listed. No other deviation.
- `rem:aging-feller` / `feller_coupling`: both laws are definitions (spacing law through run
  probabilities, restaurant law through the forward equation of the multiset of table sizes),
  both proved equal to the Ewens formula. Listed. Unlisted: the link to the urn of
  `prop:aging-urn` and the uniform colors are not formalized.
- `prop:aging-fair` / `prop_aging_fair_a`, `prop_aging_fair_b`: match. `crossing_200_bounds`
  gives `0.89245 < c_200 < 0.89255`.

## 6. Documentation changed

- `lean/PaperC/MAP.md`: module rows for `C1.*` and `C2.*`; new sections "Modules in
  `PaperC/C1/`" (14 rows) and "Modules in `PaperC/C2/`" (13 rows), labels only; the "Not in
  Lean" lists for C1 and C2 updated (`lem:admissible` and `rem:stationary` removed, the others
  narrowed); a C1 finding (`lem:layer-exact-discrete` needs only `n_i ≥ 1`); the build paragraph.
- `lean/PaperD/MAP.md`: the rows of `cor:height-window`, `thm:main-limit`, `thm:two-modes`,
  `thm:two-modes-near-one` and (split) `lem:descartes`, `lem:sp-limit`, `lem:sp-derivative`; a
  section "Modules `Modes/`" with the named hypotheses DENS, LAW, MOM; a new table "The
  coin-turning note (`S4_aging_note`) by statement label" (11 rows); module and declaration
  counts; "Build of October 25, 2026"; the "Not formalized" list.
- `lean/PaperF/MAP.md`: intro, module table, a table "Modules in `PaperF/Exact/`" (17 rows), the
  "Not formalized" list and the "Building" paragraph with the axiom check.
- `lean/README.md`: C1 and C2 bullets and counts (56, 715), Paper D counts (308, 23503) with the
  `Modes/` and `S4/` paragraph, Paper F (20, 252), and the declaration count in "Building and
  checking".
- Papers, verification sentences that had become wrong:
  - `paperD/sec_verify.tex`: it said that `cor:height-window` and the results of Section 4 are not
    formalized. It now says that the height window and the Appendix F lemmas are kernel-checked,
    and that the dichotomy of `thm:two-modes` and `thm:two-modes-near-one` are kernel-checked
    with three named inputs from `glr2026`. The threshold, the total variation strengthening and
    the bridge are still listed as not formalized.
  - `S4_aging_note/s4_intro.tex`: `MAP.md` now lists the statements under the note's labels too;
    the sentence says so.
  - Not changed, since still correct: `paperC/sec_verify.tex`, `paperC2/sec_verify.tex` (they
    list fewer modules than now exist but claim nothing false), `paperF/sec_verify.tex` ("except
    the bound in Lemma `lem:counting`" stays true, since Lean's bound is for a smaller event).

## 7. Left out or open

- `lean/.lake` was not deleted.
- `verify_lean.py` still has no `PaperF` in `LIBS`. PaperF is not in `build-log.txt` or
  `verification-manifest.json`; its axiom check is the scratch file above.
- The docstrings of `C2/BlockSegment`, `BlockReversal`, `BlockReversalLaw` and
  `MemorylessExample5` cite the research note rather than `thm:memoryless` and `ex:five-state`.
  The MAP gives the labels. The docstrings were not edited.
- `S4_aging_note/README.md` still says that the Lean map uses only the old numbers. It is not a
  verification section, so it was not edited.
- Not formalized, as the logs say: `thm:threshold`, `cor:fixed-memory-bridge`, the asymptotic
  parts throughout, `thm:pair-counts`(b) to (d), `lem:L-two`, the converse in
  `prop:layer-constants`(v), `thm:one-horizon`, `thm:generic-start`, `thm:second-moments`(ii),
  (iii), and the paper's event in the second part of `lem:counting`.
- Memory: a full parallel `lake build PaperC` with many new modules runs out of memory on this
  machine; build new modules a few at a time.
