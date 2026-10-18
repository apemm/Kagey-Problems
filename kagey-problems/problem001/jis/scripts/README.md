# Scripts for the computer-assisted results

This file is the reproduction manifest of the paper `jis/pemmasani.tex`. For every
computer-assisted result it gives the command, the working directory, the inputs, the stored
evidence file and its SHA-256, and what each stated time measures.

## Environment

All results were computed with Python 3.14.3. The packages and their versions are pinned in
`kagey-problems/problem001/requirements.txt` (python-sat 1.9.dev15, SymPy 1.14.0, mpmath 1.3.0,
PuLP 3.3.2, SciPy 1.17.1, NumPy 2.4.2, pytest 9.1.1). The SAT solvers come from python-sat
(import name `pysat`): CaDiCaL 1.5.3 and 1.9.5, Glucose 3, 4 and 4.2, MiniSat 2.2, MapleChrono
and Lingeling. CBC 2.10.3 comes with PuLP, and HiGHS with SciPy.

    cd kagey-problems/problem001
    python -m venv .venv
    .venv/Scripts/python -m pip install -r requirements.txt    (Windows; .venv/bin/python elsewhere)

Every command below runs in the working directory `kagey-problems/problem001`, with `python` the
interpreter of that environment, unless a table says otherwise. The scripts find their inputs and
write their outputs by paths relative to their own folder, so the working directory matters only
for paths given on the command line. Inputs and evidence files are in `jis/data` unless a path
says otherwise. Most scripts overwrite the stored evidence file of the same name. To rerun without
touching it, work in a fresh copy (for example `git archive HEAD kagey-problems/problem001 | tar -x
-C NEWDIR`) and compare the new files with the committed ones. Files over 2 MB are stored gzipped
(see `jis/data/README.md`).

## What the times mean

Each stored time below is read from a field of the evidence file, and the field is named.

- *invocation*: wall time of one complete invocation of the command.
- *call*: solve time of one solver call inside an invocation (`solve_seconds`). It leaves out the
  encoding and the other calls of the same invocation.
- *instance*: wall time of one instance (one width, bound or partition) inside an invocation.
- *job*: wall time of one child process of a batch, from its start to the poll that saw it end.
- *part sum*: the sum of the elapsed times of the parts of a split run (`seconds_total`). The parts
  ran on several processes at once, so this is neither the wall time nor the CPU time of the run.
- *largest part*: the elapsed time of the slowest part of a split run (`seconds_max_part`).

The column "rerun" gives the wall time of the invocation in the check of 2026-10-17 described
below, where it was rerun, and whether the regenerated file equals the committed one.

## Inventory

### R0. Section 9 programs

- `python solver/engine.py` (ILP, CBC through PuLP), `python solver/brute.py` (from the
  definition, no lemma) and `python verify_narrow.py` (the lemmas and constructions of Sections 4
  to 6, and the 5 x 5 grid) print their results and store no evidence file. `verify_narrow.py`
  exits 0 when every check passes. Rerun: `verify_narrow.py` 10.0 s invocation, exit 0.
- `python -m pytest -q tests` and `python -m pytest -q jis/tests`. Rerun: both pass.

### R1. Three rows

Theorem "three-row generating function" (b), (c), Theorem "three-row closed form", Proposition
"the class {A,B}", Theorem "the exact denominator".

| Command | Inputs | Evidence | Stored time | Rerun |
|---|---|---|---|---|
| `python jis/scripts/three_row_closed_form.py` | `three_row_reference/three_row_classes.json` | `three_row_closed_form.json` | 4.03 s invocation (`seconds`) | 3.4 s, equal |
| `python jis/scripts/three_row_closed_form_check.py` | `three_row_reference/three_row_{transfer_matrix,recurrence,classes}.json`, `three_row_closed_form.json` | `three_row_closed_form_check.json` | 1.7 s invocation (`seconds`) | 1.3 s, equal |
| `python jis/scripts/three_row_definition_check.py` | `verify_narrow.py` | `three_row_definition_check.json` | 55.2 s invocation (`elapsed_seconds`) | 24.2 s, equal |
| `python jis/scripts/three_row_formula_check.py` | `three_row_definition_check.json`, `three_row_reference/three_row_{windows,transfer_counts,recurrence}.json` | `three_row_formula_check.json` | 0.3 s invocation (`seconds`) | 0.2 s, equal |
| `python jis/scripts/three_row_symmetry_check.py` | `three_row_definition_check.json` | `three_row_symmetry_check.json` | 34.5 s invocation (`seconds`) | 10.1 s, equal |
| `python jis/scripts/three_row_orbits.py` | `three_row_reference/three_row_{classes,windows}.json` | `three_row_orbits.json` | 80.5 s invocation (`seconds`) | 62.1 s, equal |

### R2. Four rows, small widths

Corollary "widths four and five", Proposition "small widths", Table "four-row optimum counts".

| Command | Inputs | Evidence | Stored time | Rerun |
|---|---|---|---|---|
| `python verify_narrow.py` (f(4,4) and f(4,5)) | none | none | | see R0 |
| `python jis/scripts/four_row_direct.py flat 8` and `python jis/scripts/four_row_direct.py dfs 8 9 10` | `verify_narrow.py` | `four_row_direct_flat.json`, `four_row_direct_dfs.json` | 9.4 s and 84.3 s, slowest width (`results[].seconds`) | not rerun |
| `python jis/scripts/four_row_direct_check.py full 6 7 100 --cap 100` and `python jis/scripts/four_row_direct_check.py structured 6 7 8 9 10 --cap 1200` | `verify_narrow.py` | `four_row_direct_check_full.json`, `four_row_direct_check_structured.json` | 105.1 s, width 10 alone (`10.seconds`) | structured 6 to 9 in 8.4 s, equal on those widths |
| `python jis/scripts/four_row_witness_check.py` | the four files above | `four_row_witness_check.json` | | 20.8 s, equal |
| `python jis/scripts/four_row_equivalence_check.py` | `four_row_machines/*.json` | `four_row_equivalence_check.json` | 163.6 s invocation (`seconds`); the three pair sets took 36.8, 88.8 and 38.0 s (`pair_sets.*.seconds`) | not rerun (over two minutes) |

The earlier version of this file gave 89 s for the equivalence check. That is the time of the
largest pair set alone. A complete invocation checks all three pair sets and took 163.6 s.

### R3. Four rows, generating function and growth

Theorem "the four-row generating function", Corollary "growth".

| Command | Inputs | Evidence | Stored time | Rerun |
|---|---|---|---|---|
| `python jis/scripts/four_row_counts.py 1500` | `four_row_machines/*.json` | `four_row_counts.json.gz` | 5.91 s invocation | 6.9 s, equal |
| `python jis/scripts/four_row_dp_check.py 1500` | `four_row_machines/*.json`, `four_row_counts.json` | `four_row_dp_check.json.gz` | 5.21 s invocation | 1.9 s, equal |
| `python jis/scripts/four_row_recurrence.py` | `four_row_counts.json`, `four_row_machines/*.json` | `four_row_recurrence.json` | 24.9 s invocation | 20.9 s, equal |
| `python jis/scripts/four_row_recurrence_check.py` | `four_row_dp_check.json`, `four_row_recurrence.json` | `four_row_recurrence_check.json` | 3.51 s invocation | 1.6 s, equal |
| `python jis/scripts/four_row_window_check.py` | `four_row_recurrence.json`, `four_row_machines/*.json` | `four_row_window_check.json` | 44.0 s invocation (`total_seconds`) | 7.2 s, equal |
| `python jis/scripts/four_row_rho_check.py` | `four_row_dp_check.json`, `four_row_recurrence.json` | `four_row_rho_check.json` | 0.86 s invocation | 0.9 s, equal |
| `python jis/scripts/four_row_root_isolation.py` | `four_row_recurrence.json` | `four_row_root_isolation.json` | 4.1 s invocation | 31.6 s, equal |
| `python jis/scripts/four_row_growth_check.py` | `four_row_recurrence.json`, `four_row_counts.json` | `four_row_growth_check.json` | 1.0 s invocation | 1.3 s, equal |

To run the later checks on the stored counts without rerunning the counters, unzip
`four_row_counts.json.gz` and `four_row_dp_check.json.gz` first.

### R4. Five rows, part (a)

Theorem "five rows" (a). All of these read `verify_narrow.py`. The working directory of the first
four commands and the last one is `jis/scripts`.

| Command | Evidence | Stored time | Rerun |
|---|---|---|---|
| `python five_row_structured_sat.py --widths 5 6 7 ... 20 --solver cadical153 --cap 1800 --out ../data/five_row_structured_cadical153.json` | `five_row_structured_cadical153.json` | 48.5 s, slowest instance (`instances[].wall_seconds`) | not rerun |
| `python five_row_column_sat.py --widths 5 6 7 ... 20 --solver glucose4 --cap 1800 --out ../data/five_row_column_glucose4.json` | `five_row_column_glucose4.json` | 410.8 s, slowest instance | not rerun |
| `python five_row_unstructured_sat.py --widths 5 6 7 8 9 10 11 --solver cadical153 --cap 1800 --out ../data/five_row_unstructured_cadical153.json` | `five_row_unstructured_cadical153.json` | 683.1 s, slowest finished call (`solve_seconds`) | not rerun |
| `python five_row_sat_check.py` (its default schedule) | `five_row_sat_check.json` | 177.9 s, slowest instance | not rerun |
| `python jis/scripts/five_row_unstructured_dfs_check.py 5 6 7` (in `kagey-problems/problem001`) | `five_row_unstructured_dfs_check.json` | 430.8 s, width 7 alone (`widths.7.seconds`) | not rerun |
| `python five_row_summary.py --data ../data --out ../data/five_row_results.json` | `five_row_results.json` | | not rerun |

### R5. Five rows, part (b)

| Command | Evidence | Stored time | Rerun |
|---|---|---|---|
| `python jis/scripts/five_row_collar_family.py --base 8 --pad 5 --row 1 --side right --out jis/data/five_row_collar_family_w8_row1_right.json` | `five_row_collar_family_w8_row1_right.json` | 38.8 s invocation (`total_seconds`) | 18.4 s, equal |
| `python jis/scripts/five_row_family_brute_check.py --out jis/data/five_row_family_brute_check.json` | `five_row_family_brute_check.json` | 315.2 s invocation (`total_seconds`); 35.0 s for the largest board | not rerun |
| `python jis/scripts/five_row_geometry_check.py` | `five_row_geometry_check.json` | | 0.3 s, equal |

### R6. Five rows, part (c), and Remark "five-row counts"

The model cap `N` of the counting runs is not stored. Every count used in the paper is marked
exhausted in its file.

| Command | Evidence | Stored time | Rerun |
|---|---|---|---|
| `python jis/scripts/five_row_width8_candidates.py --out jis/data/five_row_width8_candidates.json` | `five_row_width8_candidates.json` | 144.7 s invocation | 52.1 s, equal |
| `python jis/scripts/five_row_structured_sat.py --widths 8 9 10 11 12 --count N --solver cadical153 --cap 1800 --out ...` | `five_row_structured_counts_cadical153.json.gz` | 40.6 s, slowest instance | not rerun |
| `python jis/scripts/five_row_column_sat.py --widths 8 9 10 --count N --solver glucose4 --cap 1800 --out ...` | `five_row_column_counts_glucose4.json` | 1703.0 s, slowest instance | not rerun |
| `python jis/scripts/five_row_count_dfs_check.py 6 7 8 9 10 11`, and the width-12 run by partition | `five_row_count_dfs_check.json`, `five_row_count_dfs_check_w12.json` | 853.7 s, slowest partition at width 12 (`wall_seconds_longest_partition`) | not rerun |
| `python jis/scripts/five_row_count_crosscheck.py 5 W` for W = 8 to 23 (runs `row_bound_count_dp.py`) | `five_row_count_crosscheck_h5_w{8..23}.json` | 185.4 s invocation at W = 23 | not rerun |
| `python jis/scripts/five_row_optima_dp.py 5 W` for W = 13 to 23 | `five_row_optima_dp_w{13..23}.json` | 66.97 s invocation at W = 23 (`results[].seconds`) | not rerun |

### R7. Six rows, part (a)

Theorem "six rows" (a).

| Command | Evidence | Stored time | Rerun |
|---|---|---|---|
| `python jis/scripts/six_row_structured_sat.py W A` and `python jis/scripts/six_row_structured_sat.py W B` for W = 9 to 14 (default cap 1800 s) | `six_row_sat_w{9..14}_{A,B}.json` | 171.5 s, slowest call (`solve_seconds`, W = 14, encoder A) | not rerun |
| `python jis/scripts/six_row_sat_check.py batch jis/data/cells_check/ssat_jobs.json CONCURRENCY CAP` | `cells_check/ssat_jobs_summary.json`, `cells_check/ssat_w{13..16}_p*_cadical195.json` | 760.2 s, slowest job | not rerun |
| `python jis/scripts/six_row_dfs_check.py W P 1200 jis/data/cells_check/dfs_wW_pP.json` for W = 9 to 13 and P = 0 to 9 | `cells_check/dfs_w{9..13}_p*.json` | 948.3 s, slowest partition (`seconds`, W = 13, P = 5) | not rerun |

The concurrency and the cap of the `ssat_jobs` batch are not stored. Every job of that batch
finished, so the cap did not bind.

### R8. Six rows, part (b)

| Command | Evidence | Stored time | Rerun |
|---|---|---|---|
| `python jis/scripts/six_row_structured_sat.py W A` and `... W B` for W = 15, 16, 17 (witnesses, and the collar board of S_16 with two enumerators) | `six_row_sat_w{15,16,17}_{A,B}.json` | 304.7 s, slowest call (W = 17, encoder A) | not rerun |
| `python jis/scripts/six_row_witness_brute.py jis/data/six_row_witness_brute_w15_17.json 1700 jis/data/six_row_sat_w15_A.json jis/data/six_row_sat_w15_B.json jis/data/six_row_sat_w16_A.json jis/data/six_row_sat_w16_B.json jis/data/six_row_sat_w17_A.json jis/data/six_row_sat_w17_B.json` (third enumerator) | `six_row_witness_brute_w15_17.json` | 25.4 s invocation (`total_seconds`) | not rerun |
| `python jis/scripts/cells_witness_check.py` (every stored witness and collar board) | `cells_witness_check.json` | 15.5 s invocation | 12.5 s, see the check below |

### R9. Small grids

Theorem "the guess fails" (a), and the stored blackouts of h+m points of Section 9.

| Command | Evidence | Stored time | Rerun |
|---|---|---|---|
| `python jis/scripts/small_cells_sat.py C` for C = 5x6, 6x6, 6x7, 6x8, 7x7, 5x7@12, 6x8@16, 6x8@17, 7x7@16 | `small_cells_sat_{5x6,6x6,6x7,6x8,7x7,5x7_b12,6x8_b16,6x8_b17,7x7_b16}.json` | 1577.5 s, slowest call (`runs[].solve_seconds`, 7 x 7 at bound 15, CaDiCaL 1.5.3); the six calls of that invocation took 4261 s together | 5x6 in 2.6 s, equal |
| `python jis/scripts/small_cells_split.py 7x7 15 J A` and `... 7x7 15 J B` for J = 1 to 7 | `small_cells_split_7x7_b15_case{1..7}_{A,B}.json` | 858.9 s, slowest call | not rerun |
| `python jis/scripts/cells_sat_check.py batch jis/data/cells_check/sat_jobs.json CONCURRENCY 1200`, and the same with `sat_jobs_satcases.json` | `cells_check/sat_*.json`, `cells_check/sat_jobs_summary.json`, `cells_check/sat_jobs_satcases_summary.json` | 1001.4 s, slowest finished job; one job (7 x 7 at bound 15, CaDiCaL 1.9.5) was killed at 1201.4 s and is unresolved | not rerun |
| `python jis/scripts/small_cells_ilp.py highs` and `python jis/scripts/small_cells_ilp.py cbc` | `small_cells_ilp_{highs,cbc}.json` | each instance stopped at the 1800 s cap (`seconds`) and gives no bound | not rerun |
| `python jis/scripts/cells_witness_check.py` | `cells_witness_check.json` | 15.5 s invocation | see R8 |

### R10. Table "computed values", the counts on 5 x 6 to 7 x 7, and f(7,8) = 16

| Command | Evidence | Stored time | Rerun |
|---|---|---|---|
| `python jis/scripts/table_counts_sat.py HxM@K --out jis/data/table_counts/sat_HxM_K.json` (Glucose 4) | `table_counts/sat_*.json`, `table_counts/sat_digests.json` | 1745.1 s invocation (7 x 7) | 5x6@11 in 1.5 s, count 76, model digest equal |
| `python jis/scripts/table_counts_sat2.py HxM@K --out jis/data/table_counts/sat2_HxM_K.json` (MiniSat 2.2) | `table_counts/sat2_*.json`, `table_counts/sat2_digests.json` | 511.8 s invocation (6 x 7) | 5x7@12 in 7.1 s, count 1184, model digest equal |
| `python jis/scripts/table_counts_search.py HxM@K --out jis/data/table_counts/search_HxM_K.json` (column search) | `table_counts/search_*.json` | 1776.7 s invocation (6 x 7) | 5x6@11 in 4.2 s, count 76, model digest equal |
| `python jis/scripts/table_counts_sat.py 7x7@14 --split N --out jis/data/table_counts/satsplit_7x7.json`, and the same for `7x8@17` | `table_counts/satsplit_7x7.json`, `table_counts/satsplit_7x8_17.json` | 7 x 8 at 17: 128 parts, largest part 174.2 s, part sum 2952.3 s | not rerun |
| `python jis/scripts/table_counts_sat2.py 7x8@17 --split N --out ...`, and the same for `7x7@14` and `7x8@16` | `table_counts/sat2split_*.json` | 7 x 8 at 17: 128 parts, largest part 569.4 s, part sum 3870.0 s | not rerun |
| `python jis/scripts/table_counts_search.py 7x7@14 --split N --depth 2 --out jis/data/table_counts/search2_7x7.json`, and `6x8@15 --split N` | `table_counts/search2_7x7.json`, `table_counts/search_6x8.json` | 7 x 7: 16,384 parts, largest part 288.28 s, part sum 46,531.52 s | not rerun |

The number `N` of worker processes of a split run is not stored and does not change the result.
The 46,531.52 s of the split 7 x 7 search is a part sum. It is neither the wall time of the run
nor a measured CPU time. The whole-grid runs on 7 x 8, and the whole-grid MiniSat run and column
search on 7 x 7, stopped at the 1800 s cap and are recorded unresolved. `table_counts/summary.json`
collects the counts.

### R11. Six rows, widths 9 to 14 (open question 2)

| Command | Inputs | Evidence | Stored time | Rerun |
|---|---|---|---|---|
| `python jis/scripts/six_row_collar_6x9_check.py` | `small_cells_sat_6x9_b16.json` | `six_row_collar_6x9_check.json` | 6.8 s invocation | 8.1 s, equal |

## Batch drivers and solver deadlines

`cells_sat_check.py` and `six_row_sat_check.py` run their jobs through `batch_jobs.py`. A batch
accepts a child result only after the child exits with code 0, and only from a fresh attempt file
whose name carries the job key, the SHA-256 of the parameters and of the scripts the child
imports. The attempt must be complete JSON with that job key, the same parameters and input
hashes, and status SAT or UNSAT, and a SAT witness must be valid and of the size asked for. The
accepted file is then renamed onto the output path. A failed or rejected job publishes an "error"
record, and a job killed at the cap an "unresolved" record, both by an atomic rename, so an old
file at the output path is never read back as a new result. The batch exits with code 0 only when
every job ended SAT or UNSAT, with 1 if a job failed, and with 2 if a job was killed at the cap and
none failed. Without `--overwrite` a batch writes nothing and exits with code 3 when the output path
of some job already exists, so a rerun cannot replace a stored file by accident. `JOBS_summary.json` records each job with its status and the reason. The tests in
`jis/tests/test_batch_drivers.py` check this refusal, plant an UNSAT file at the output path of a
job with a broken backend, run the batch with `--overwrite`, and check that both this job and the same job without the planted file end as error and
that the batch exits nonzero.

The stored `cells_check` results were made by the earlier drivers, which did not test the exit
code. The command
`python jis/scripts/batch_log_check.py jis/data/cells_check/sat_jobs.json jis/data/cells_check/sat_jobs_satcases.json jis/data/cells_check/ssat_jobs.json`
compares each stored result with the last line of its child log, which the batch opened fresh for
that child. On 2026-10-17 all 87 SAT and UNSAT results matched the result line of their own child
log. The one other job is the unresolved one killed at the cap, with an empty log.

`Solver.interrupt()` does not stop CaDiCaL inside pysat (`solver_interrupt_check.py`, with the
result `jis/data/cells_check/solver_interrupt_check.json`). So `small_cells_sat.py`,
`six_row_structured_sat.py`, `five_row_enum_types.py`, `five_row_enum_unstructured.py` and
`verify21_sat_check.py` run the solver in a worker process (`supervised_solver.py`), and the
parent kills it at the deadline. A call that reaches the deadline is recorded as unresolved, and
a backend that fails raises an error instead of returning a status. The tests in
`jis/tests/test_supervised_solver.py` check this on a pigeonhole instance with CaDiCaL 1.5.3 and
1.9.5. The table-count scripts use Glucose 4 and MiniSat 2.2, which stop on an interrupt. The
scripts `five_row_enum_points.py` and `five_row_enum_structured.py` test their wall-clock limit
only between solver calls, so a single call there is not bounded.

## Fresh-environment check of 2026-10-17

We made a fresh copy of the committed folder with `git archive HEAD`, added these scripts, made a
new virtual environment with `python -m venv` and `pip install -r requirements.txt` on Python
3.14.3, and ran the commands that have a rerun time above. Each regenerated file was compared with
the committed one after dropping the fields that record times, dates, versions and paths. Every
compared file was equal, with two kinds of difference, in four files, that change no result.

- `cells_witness_check.json`. The rerun checks 12 stored small-grid files and the committed file
  10, since the committed file was made before `small_cells_sat_6x6.json` and
  `small_cells_sat_5x7_b12.json` were stored. The rerun finds no problem in any of the 12, and its
  six-row and collar records equal the committed ones.
- `table_counts/sat_5x6_11.json`, `table_counts/sat2_5x7_12.json` and
  `table_counts/search_5x6_11.json`. The committed files were written before the scripts recorded
  `models_sha256` and `first_column`, and they list the first models in another order. The counts
  are equal, and the new model digests equal the ones stored in `table_counts/sat_digests.json` and
  `table_counts/sat2_digests.json`.

The long searches were not rerun.

## Other files

`batch_jobs.py`, `supervised_solver.py`, `cells_common_check.py`, `five_row_common.py`,
`five_row_sidevec.py`, `four_row_machines.py` and `verify21_common_check.py` are shared code.
`cells_check_summary.py`, `cells_sixrows_summary.py` and `five_row_summary.py` collect results.
`evidence_manifest.py` checks the hashes below and `batch_log_check.py` the batch logs. The
`verify21_*` scripts and `five_row_w21_compare.py` recheck an earlier five-row witness of width
21, which the paper no longer needs, since the width-8 blackout covers every width from 8 on.
`make_jis_single_file.py` builds `pemmasani_jis.tex`.

## Evidence hashes

SHA-256 of each evidence file as committed, for text files with LF line ends. Check them with
`python jis/scripts/evidence_manifest.py --check`. The child logs (`*.log`) are not listed.

```
# R1 three rows
e3aba1c46f55aeaf1f830f5096a29d229e748fedac391f856ee0d17568512373  jis/data/three_row_closed_form.json
35b5be6a880737f9b5dd3c7404e37dd4941b2a36fbd09862cf28c3b2a062a8a1  jis/data/three_row_closed_form_check.json
691ae0821224386c5187d4c3aab9c31c48b524e3eeeb12afe275ba5945916b6d  jis/data/three_row_definition_check.json
848e695f0c01ec5dabfd14a2514bd23ef974460c924460132a963582225e2433  jis/data/three_row_formula_check.json
d4d844bb8f0a56cae645d6aca165bd64d7a2a88df679154ccfb5803c341ae0f3  jis/data/three_row_orbits.json
223f7bec093bc1782e5ba097dd1012b8006d35da532dc81e980b21a479d4fb20  jis/data/three_row_symmetry_check.json
b30fd38a6c3a26b4e13015e4f216eaad6a5208a901aecc52e56608de72d02c83  jis/data/three_row_reference/three_row_classes.json
f3e17452acc6491cffe65aba97ff89fc2c05f31b0320613199420872ff3e79e3  jis/data/three_row_reference/three_row_recurrence.json
6d4ba73b836689803589023745bf1a7850004f0093e3dc8fb72a7a9e303d71df  jis/data/three_row_reference/three_row_transfer_counts.json
f3177048da0176cf675ef5d4a2af7389b514ea540473f8b6bad2bc7b8e994784  jis/data/three_row_reference/three_row_transfer_matrix.json
7d54d7c3051498cdb83ca6ed67644e64ce850bc117f6b4e588c6bbfda043f162  jis/data/three_row_reference/three_row_windows.json
# R2 four rows, small widths
25ba7a1f241c54e97276050c2d61fdef08fab8ad67d2570e5733e94cfa142821  jis/data/four_row_direct_flat.json
12c449bb35c7a07551f773452325a7dd404dc3516ca152476267e3c726eaa287  jis/data/four_row_direct_dfs.json
61913e924d057b3348819267a52a6cb0d62eba23f0cb7586135adfd7134c8ce5  jis/data/four_row_direct_check_full.json
e3b7e8ad5415d8345c9dfb2d7729fca948058392b242431eeace8241684d75b6  jis/data/four_row_direct_check_structured.json
c36b4477ef25a88a01e2ded346bbc6e7288fba59362fd52f3c15ab1150a26b1d  jis/data/four_row_witness_check.json
6eb1b11b543e3a6b07c3bf6b040c43ca64a7723abf1229f487a475e9cb935526  jis/data/four_row_equivalence_check.json
b30199b00a616a3095ffdf1a81bf4af629cdd01d4b3283bb32b50f66207f6bba  jis/data/four_row_machines/machine_351012.json
26779f35d6a75fa477045d83749f46189efdcac65293d14d81326ad1639dcb3b  jis/data/four_row_machines/machine_36912.json
7c6d5c83ebfaaf2ae03d0b1569d1ec03452653b86182d4eab8fd7a419207efae  jis/data/four_row_machines/machine_56910.json
# R3 four rows, generating function and growth
eabcc5fa70133f62425b18c3153aeacd4a9f7a82b4fd4efda235a693d5e8213c  jis/data/four_row_counts.json.gz
d6ea3627546d5a98c2f3ed3030c793b4dda3809a0b3aa48d8f9dda1f3b083f68  jis/data/four_row_dp_check.json.gz
3c88c73bd9b0d5c304171e254bb325378a30b787d5653142c664fe2a22f34fbc  jis/data/four_row_recurrence.json
a10858ff27d30142bd89b946fadf04eb66067b25d209658c68ed8a5e12048ecd  jis/data/four_row_recurrence_check.json
8c3f903875369f7c91af5524e13de478078deb6acc4b161069a3201242a38a71  jis/data/four_row_window_check.json
3126f96c0e49711bfa30cdc7ebb89447a723b3d1ece10f3fca37dfc27b948b25  jis/data/four_row_rho_check.json
ac674a3ec835334d263ced3c91b50537da90efebcfb9dac60b987d4cee49c326  jis/data/four_row_root_isolation.json
47620736ed5f00ba6523c664ed4af3237e0a88808ba1f01d5e56cc43cfc1ce6a  jis/data/four_row_growth_check.json
# R4 five rows, part (a)
d676df1ef81f8346b20c70153447b265bf7c71394bc2530134c134756bd7d00f  jis/data/five_row_structured_cadical153.json
90f43886b81dcf917b6b96b33c68dfb99ebcf44fd903da489f423228258b6ba4  jis/data/five_row_column_glucose4.json
c1550804ffb9cfb1738d728ef5bba373a13bb6c61a4984bf1565c6874d140a61  jis/data/five_row_unstructured_cadical153.json
1ffbf9ebfc0e45be38095d79ca509071e93cf538789782c2af257778bb8bdde1  jis/data/five_row_sat_check.json
2ecc46b232c970dc8d03a1f9d0afcdf35f7845fb0f2d39160b0b889db7e30e9a  jis/data/five_row_unstructured_dfs_check.json
ee7c797018eeabbb532a2e67536d3e9b28e119f92032c467e612a98592120a46  jis/data/five_row_results.json
# R5 five rows, part (b)
61904ed96741b9b9d21ec139cb8e9d7ddfdfdeb7255017804fd8aa9b0b83fab9  jis/data/five_row_collar_family_w8_row1_right.json
b7382112e0dd83812dc47b324b8ce118c85c8b8ac967158e1c23ed13db55fdd1  jis/data/five_row_family_brute_check.json
4691ebdb9406a74cb628131e9ca28684f02914699ca65a3d5d24decec8e6f511  jis/data/five_row_geometry_check.json
# R6 five rows, part (c) and the counts
8776c4da107e7d3576d86c1b39b29f6138cbc185ef2585bac7e057bf852324fa  jis/data/five_row_width8_candidates.json
783672c0351334bb267758285ac9a596ef9c9ca27914c84736e8de53cfff61b1  jis/data/five_row_structured_counts_cadical153.json.gz
472345ef17a7e2619ce6b1f0406c3ad832abef24158fb883fad88dbeac4542c4  jis/data/five_row_column_counts_glucose4.json
bac783b4a08edafe91eca27cdc9b2896830d6012bea9e88ee9088bfde0bdcb1b  jis/data/five_row_count_dfs_check.json
0bf8df47b78b5ff61f68634d112adaee3ffba4a9e9281faa8a980d06d8361df1  jis/data/five_row_count_dfs_check_w12.json
31f15ae8ce5c634bc29f868651e2f324f66a0942a53f86f81a67a13d336a3e28  jis/data/five_row_count_crosscheck_h5_w10.json
869d20aaf792a307076868b9276dfb8ac699fa98c737fbf75ca94cfb797f0190  jis/data/five_row_count_crosscheck_h5_w11.json
1c9e86d4c86b2d470071e5aeb06c2dcb5f6af1ff8554a0cfaa73cd30cb0e2407  jis/data/five_row_count_crosscheck_h5_w12.json
1a4cd9890310704022c5a4111230f5ec02d4d4136b57ffcb213a60dd23fdb485  jis/data/five_row_count_crosscheck_h5_w13.json
f3b821f36fa929e1a480087baad035c32995c0f43a016f3becf3d87eb9b4b6de  jis/data/five_row_count_crosscheck_h5_w14.json
c990f6a366278d948aacf69dd5adb84a7f04942bca5fdba67bf446b58878d1a2  jis/data/five_row_count_crosscheck_h5_w15.json
9efe4ce2ce3122aff7792109704878164257747c0cddbf541eb99898513643ce  jis/data/five_row_count_crosscheck_h5_w16.json
efff2e7c257a194a76477a6024569f327904e3e899aa2137ff79b368b41309f1  jis/data/five_row_count_crosscheck_h5_w17.json
6322080838b6b6325a12971b74aebf19ad3d242407effb1847da0ca5e5caf93b  jis/data/five_row_count_crosscheck_h5_w18.json
207b71661576dd8b22ec480161726eb328e2d09b98734fee10cedecb0cb51038  jis/data/five_row_count_crosscheck_h5_w19.json
38f9f28805d74fc6eaa1a0e29f74a3ac8a4c5e1bd9dad34184d749381db8fe67  jis/data/five_row_count_crosscheck_h5_w20.json
238879cb0df2a700144e7d94a958c4ee2bc8f9f2a708d6eb14d395a8ec74c1df  jis/data/five_row_count_crosscheck_h5_w21.json
2818719f7b6baeb819751af396b249a9aaaf855ed57484babb92a3b057b6830e  jis/data/five_row_count_crosscheck_h5_w22.json
b15c3d325cbde445ebffdf336e824bcd0bce0265738d804659ff320916e001c7  jis/data/five_row_count_crosscheck_h5_w23.json
43b67bbbe0de135fd018f056503b684a183646c49cbeacbf87aed34078f86f17  jis/data/five_row_count_crosscheck_h5_w8.json
63c9f2eab32a686ac58580c6063321af3d61fc956b0f3dc376a142cad8c7acc5  jis/data/five_row_count_crosscheck_h5_w9.json
ec2a44cbc6c468422b4030d33d5dfb17705254d0c7cdb08be0e3484cd1a30fc4  jis/data/five_row_optima_dp_w13.json
8fd0fdbb07d2e785f81a38e6b19368eba2e7e127a9a06bbacd81c4d3bac826ca  jis/data/five_row_optima_dp_w14.json
b5be2d15832a64a7a374d8ba88a63529cf81fda9e36e474d25916f9020c09733  jis/data/five_row_optima_dp_w15.json
d1de62352e7137828b69b14544fb1f26ce5d327a0c95fb6b003f8f53df465752  jis/data/five_row_optima_dp_w16.json
081c07de5664c4507f9bbd74311117cfbaef9ad1268f4aa2582d2ee2e458cf03  jis/data/five_row_optima_dp_w17.json
9c058cf78332c381917f8034bd31843cd644ae2be3929245b9a1eb7f0731f472  jis/data/five_row_optima_dp_w18.json
46091ab56872cd8c5b32061bd00be20801ec1c5f187c78720eadcce7b35266e2  jis/data/five_row_optima_dp_w19.json
8e3c936731f4860aa61f6668d0926568ac2db1cc51be8d832b58a838c40a141f  jis/data/five_row_optima_dp_w20.json
39a2b24fe2d555d286e22152275383c59b723e583e48a5017d387f59823f0c49  jis/data/five_row_optima_dp_w21.json
c7398530d2ae4d4fc313f7054a6d093ccb760789a4ee33ac622b38b80b71f31c  jis/data/five_row_optima_dp_w22.json
80e663894f0e3b191eccadc9bca4ebf7b24f92ee513f5cf77427becccf939ba4  jis/data/five_row_optima_dp_w23.json
# R7 six rows, part (a)
69746449c35e415819b4d2548772187b87d93054b508bfe84f5d66a8087bc1bb  jis/data/six_row_sat_w9_A.json
16c9cebf2a94f413094d9ce1bedb207b7d1c1073898c20fc98f0fe7bcba06b50  jis/data/six_row_sat_w9_B.json
1049b18b6c9ca08ba71033a4328dd56fc0e859e9bd44b6fcebd16b0c180f84a0  jis/data/six_row_sat_w10_A.json
ec89c58aeac21b2b845150dd2597d569efe699c851815dee65398fc853f0dea3  jis/data/six_row_sat_w10_B.json
0bcd5a86e489ba5e52b07b94731b31b68b3e8abe4cd052ed75660d9deca4326d  jis/data/six_row_sat_w11_A.json
37276f84f6cfa3bc1c48088a8c9e4fa8f9aea1a0c9772a9d50998f917dc29a87  jis/data/six_row_sat_w11_B.json
4146caec0497700c3de20d566830cdf38506b1fd5fd0ad02a5f86ec4216da9b1  jis/data/six_row_sat_w12_A.json
24f5fe9bd4feb738a4a151c21e3e0922c1d679dd94544e3594c2737eeb49c885  jis/data/six_row_sat_w12_B.json
d083cd7a0c7e5b02ac02e4464ed24cd119ef8c168d8a62fcc7e579d399afa848  jis/data/six_row_sat_w13_A.json
6639bc8504d666a26fb65c851ad51c2c623697b67097d588f68ae98c1c1b5777  jis/data/six_row_sat_w13_B.json
4fe2ff3977b58a9124360934bde9ef6c90dd189d5a9c4b417f9bafe2acfe5965  jis/data/six_row_sat_w14_A.json
139c9fd8da2e72f6db4614e03e58c93d86183f81fb7da07a7f0fe30043f83c1e  jis/data/six_row_sat_w14_B.json
c7a99805fbdddda9298b77e6998db6fbf52d4c2b32c1aac0e52bac034e2bbd14  jis/data/cells_check/ssat_jobs.json
3b986491403e77d19cc00c866ff8f24069f0d14c466db30d35a8af3f271e0692  jis/data/cells_check/ssat_jobs_summary.json
defd21345e38ce635956a3a0c4af9ef75dff3a77887c83adc409df676b8e7d0e  jis/data/cells_check/ssat_w13_p0_cadical195.json
0ef420f3449a5199bf1274274e25c3301dd7f5ceb9b8d16f50b4250c16ce4efd  jis/data/cells_check/ssat_w13_p1_cadical195.json
43489964fcfe26bc792a54b43de90031bdd8f189e8f2fdfe5bf16b9411fe2594  jis/data/cells_check/ssat_w13_p2_cadical195.json
e5a5858f62d7a9101d390ac63dadce9e8c1f71a5be457bbcd06972b2eeab82c8  jis/data/cells_check/ssat_w13_p3_cadical195.json
f9bcc1b22482a44a811514ef7ab8b9fe87b520cd88a057da810d4100f25c1f18  jis/data/cells_check/ssat_w13_p4_cadical195.json
3c2dfb382507e30f673cc389dcc642c41e3cc010af69c40df11fcf87a02ecb65  jis/data/cells_check/ssat_w13_p5_cadical195.json
cb179da44c9351da142c0f04983d553bd6052724bf55d476d507002c328de48d  jis/data/cells_check/ssat_w13_p6_cadical195.json
6e360512e0ba75f374c6e78be9dab8cffb776da79b6eb6a99843f074e50f6a94  jis/data/cells_check/ssat_w13_p7_cadical195.json
e8e3a67bea31824c0c5e09ef6d54dce5c146503a9da5c75291cb71f99e82bd13  jis/data/cells_check/ssat_w13_p8_cadical195.json
2491b69734b08b07e5930cd6f95538c6a999a15d6223612f0bf07187d112c8b3  jis/data/cells_check/ssat_w13_p9_cadical195.json
915feab3311a7531302f51f4e651a8874cb0978b498b46a12cd56c1ffb35a711  jis/data/cells_check/ssat_w14_p0_cadical195.json
bbd511f8cf45be7ab6381a1a1f002c495f4b6de402a74faf2e4616732d9a2408  jis/data/cells_check/ssat_w14_p1_cadical195.json
68057c3aac0da304c3b5d7ee09f4b5d7765e3c3e813130cf8bf415f9f5c5e897  jis/data/cells_check/ssat_w14_p2_cadical195.json
e9a775f2cbcaf4d7b6d99daa241c05f9267b890d6ad59cdd6047357842e5f4d0  jis/data/cells_check/ssat_w14_p3_cadical195.json
28c89401b0377c4010c01be312ed87a6d142d49f8c44d02433f9cc5ea1158b3b  jis/data/cells_check/ssat_w14_p4_cadical195.json
ecd484a1ef2d9d32210cfe6016e4c4686f9079784d14d7877939ce84e210fca7  jis/data/cells_check/ssat_w14_p5_cadical195.json
8a4adfd53bcdd90bf3b49434124d4986725c4a684f97c8fe27dbe75a180bd56a  jis/data/cells_check/ssat_w14_p6_cadical195.json
2a5cc7cddcf9221b4c628cfcbe3e193e247df787b0eddfff1bb7eaba19e74043  jis/data/cells_check/ssat_w14_p7_cadical195.json
daac6fdda6d7ef18ae1738a35444d383f40e349a072247408a105cb9979a832f  jis/data/cells_check/ssat_w14_p8_cadical195.json
b34160f2da7f2bc9ed8f43d6893cf18341a47b3559b24e19fb5eb1479faa3237  jis/data/cells_check/ssat_w14_p9_cadical195.json
a7c49b87b9847e5458071b104cc306ac189ff9186ed263c27dcb3abba79f502c  jis/data/cells_check/ssat_w15_p0_cadical195.json
55ba4a364c1a7a5004bd7509c9b02403797020a8407583525ab5d38b2772880e  jis/data/cells_check/ssat_w15_p1_cadical195.json
dd8a24672b8d6619ddcef0880e90c91483bc16aef2f639a50bb7b49187f37fe8  jis/data/cells_check/ssat_w15_p2_cadical195.json
3cd93f949d272a9776e57d83d83c9821055195870827868add310b7de1b067d8  jis/data/cells_check/ssat_w15_p3_cadical195.json
b48b0e77e85052ba3c6fad656e6cc6c05ad42ccf4280973b9a56d962f0faef9b  jis/data/cells_check/ssat_w15_p4_cadical195.json
c8b0e89af9f298577751c1ea18c1feb6b3e9e3aa9bf9db06289cdb5f675eb894  jis/data/cells_check/ssat_w15_p5_cadical195.json
204add06e4457901c31e2fc9d3f9275cf25662507683b14e652e1400a3daddd6  jis/data/cells_check/ssat_w15_p6_cadical195.json
eb5ccb452df3064f9a7aabd560bc614243ee6940bc6fb51faea659606f872dae  jis/data/cells_check/ssat_w15_p7_cadical195.json
91f21a15f8810f964896a5d71c65c78db5275d3561fd509650e7aa7fcb598a57  jis/data/cells_check/ssat_w15_p8_cadical195.json
02f46bfd1d2d18935a2876c124cec69d22688c97b829523df086726e9711a459  jis/data/cells_check/ssat_w15_p9_cadical195.json
cd5b73941562ba3b34ac19d97c827124a43ae7671deb5213c223588d4804607e  jis/data/cells_check/ssat_w16_p0_cadical195.json
bd634bf5d877a9cb33b6a9f47639642c5a656be308cbb03194664b50038f0e46  jis/data/cells_check/ssat_w16_p1_cadical195.json
4b7e3805c5dd75ff15e59aafb8e816a0b53d75af2404021d5239130c68c6f9b1  jis/data/cells_check/ssat_w16_p2_cadical195.json
2f74660d079212afda0b0d52031a9b993624d886fe11da54d27ff59d2de8d14c  jis/data/cells_check/ssat_w16_p3_cadical195.json
b26b459e3c95be480d414745085735ab7c1ce8b54e46291f52daed44efa9f213  jis/data/cells_check/ssat_w16_p4_cadical195.json
ee7772b0058c5fa754f7d9663c9ccc66d5df0e4af47d1e0c448dd631954ac5bd  jis/data/cells_check/ssat_w16_p5_cadical195.json
718600e9859b1e93426b49bd72cc794ea6e708e22ac9a236d5ab18a5b3d1efbd  jis/data/cells_check/ssat_w16_p6_cadical195.json
ddd382f5c19629b3a9567cbadb2e8ea8fae9cba87f1a02f641d6bb0c06e70e6e  jis/data/cells_check/ssat_w16_p7_cadical195.json
b5299e8aa7441e8550539885d5fa8dadfa0ca95aebaa49a5b500956315bfedb6  jis/data/cells_check/ssat_w16_p8_cadical195.json
d32d7bf1ca027e130b335cdc25a2507066469c9436780781ec327b1ce72a9eb5  jis/data/cells_check/ssat_w16_p9_cadical195.json
0822045def36277941da9cdcd8af0c7ecb905c17a824fabda26319b16d7b9efe  jis/data/cells_check/dfs_w10_p0.json
6ff4bd16850d11a724ca1a48e0310383aff25d44a570f5c2ca3e580654398791  jis/data/cells_check/dfs_w10_p1.json
d0818988a4edd1f5fc63db64f7abe31e4db184709756da08c95def4cbc5f4eb3  jis/data/cells_check/dfs_w10_p2.json
6078c91a7a1925c539d56762aa1f534aa4e2db9ad9577aacadf8ef6af9f7c52e  jis/data/cells_check/dfs_w10_p3.json
c85905eaabd8a105a089443a73c2b66cc42b0f6afc30c5c71528e76e1b9b22e8  jis/data/cells_check/dfs_w10_p4.json
e4aaecb9426f28f4cd9d8dcfa74842fe4c74d1c8f10d0188b5f56b2f1b9a5a41  jis/data/cells_check/dfs_w10_p5.json
c73d280106ecb688f1a915e14e90a8b910db2f729802ae43d04257b5baa4cd81  jis/data/cells_check/dfs_w10_p6.json
a850c0c55ecb0b9bc4dce41bed98668edbd930cc631743f6e34df6c8d1701768  jis/data/cells_check/dfs_w10_p7.json
36179f7a371a304606dbd37cfec49e7298e398ad36af2d42095e04143e21c3b3  jis/data/cells_check/dfs_w10_p8.json
a01253605ec538d58f673dadcf06091b4e77e12569ceeef8ef83e3772413a630  jis/data/cells_check/dfs_w10_p9.json
3de4363fd19d25f51d8a3a003abbfba7594c5fa48d05dd87fe6e2c6142c9a4d5  jis/data/cells_check/dfs_w11_p0.json
9e1a9610d792071608a135bf74783a7ab29037c6bcc2f11a452770ec195a0cb6  jis/data/cells_check/dfs_w11_p1.json
c2bd8cb7a2d893fc30e6e4a3d5de3c448bba6f58ea31c1dcae0bcb09b6284703  jis/data/cells_check/dfs_w11_p2.json
05b71c73a8a6c717e2a8032a24ae987d7cd55fc802d6799c05fd4f9b68f9e4a4  jis/data/cells_check/dfs_w11_p3.json
3e9c7ebf61588b804159e9490bfae4ceaa6d630e2d979e397a041b6ae04aa2dc  jis/data/cells_check/dfs_w11_p4.json
1ae313b9c0e108a3cc6d986c74b9497740e5d0655a3babaa6446a69b439bb5bd  jis/data/cells_check/dfs_w11_p5.json
04f788d5767b7f1e8d6103f8cd01f965fef83b0e2306ac22910e3ced88624127  jis/data/cells_check/dfs_w11_p6.json
2d6e9c15d42743846bf384914f1c0f8c5aaf340bf9c4e8f0a90ee06abda7b1ba  jis/data/cells_check/dfs_w11_p7.json
24a9141b8ab5f871c7bbfa4fe16eba7ccdbf4d4917256216edbc396af03a81e3  jis/data/cells_check/dfs_w11_p8.json
001c4f1282d637afa2c2050691b4dd534559913d2a4d45fe848631c65282b0b3  jis/data/cells_check/dfs_w11_p9.json
d400a22efd5c06ee41303c6b103f01dcb85b8cab82685705365eda5f0a51389b  jis/data/cells_check/dfs_w12_p0.json
b43479b0f5f474c9d1dbec44bf0400041dce2f4e4f8d558820ad343a79423aa7  jis/data/cells_check/dfs_w12_p1.json
305cc546553ad23447656bbb0f4ad98a85670fc0201ee697b6672b8a4e29b635  jis/data/cells_check/dfs_w12_p2.json
ad391f16d74bf2a86e7d31fcaa97657295ec6828aafff4e2dcb825f2eab450eb  jis/data/cells_check/dfs_w12_p3.json
82eee9cf8e36ed76cd625af4156e559bf8c9bfd24f166a40cd221e28146db6fd  jis/data/cells_check/dfs_w12_p4.json
8073d3826137b1a9f674f20557a129a88171c4204a8c33127779c0b8cd50b502  jis/data/cells_check/dfs_w12_p5.json
cad5a7ba867a1354cc983dddab23e9d3b35c605b2d4982aa34189706bed96ec8  jis/data/cells_check/dfs_w12_p6.json
46106aa18cc4fbd865b418cd7ca543ebf1c81049bdf30b16dc34df3fdfe70c75  jis/data/cells_check/dfs_w12_p7.json
b63bbeb10e7c000e709eeeba7ec0a384cbaf8b0df9e79b5e7c24de9e707b387c  jis/data/cells_check/dfs_w12_p8.json
ffcf03df592c086c2260d2f6ce4c24cfe7d15f331146f264c16d9d9c27d2c649  jis/data/cells_check/dfs_w12_p9.json
31841b96688369ab09636fc7819e7d92f0a719831396be8ff6b6c6c562a15288  jis/data/cells_check/dfs_w13_p0.json
cc6b7b4ae9134962639d347bbb052c15bcc0ef84642c16354cc41ea3254fb98e  jis/data/cells_check/dfs_w13_p1.json
90c8fc1f19c365bacc2290f443e5ac232ada3e6d02ce64027b9ed9bf7c1a531e  jis/data/cells_check/dfs_w13_p2.json
34fd759df522175cbd04f929cd83fec0674efa11f3a785816d7b91c991fb541d  jis/data/cells_check/dfs_w13_p3.json
7b606e200e29af54e2b0e612faba6b4ed6265cace4cc53189870a5ef76340002  jis/data/cells_check/dfs_w13_p4.json
f605bc2530647165441fc9aae070c803f523b053b1be5bb29fa40a73414cca9a  jis/data/cells_check/dfs_w13_p5.json
b923fa158f9e4cc33b521f06acdb1b5c916ec54c37ef908ecd1c03b4feba923e  jis/data/cells_check/dfs_w13_p6.json
dee37813c733854715e609afb54ca518a6c9e2c6a7f40cb116970d7441ad335f  jis/data/cells_check/dfs_w13_p7.json
51e371dffc6918e3ec5df5a9b07ad9f701ffd6176a058c4b3c3ba3c6e18b205d  jis/data/cells_check/dfs_w13_p8.json
ccdc1723e4f30c7db90285ff1b3fd2a0fe39234ed8d1be72b588df215b06b93e  jis/data/cells_check/dfs_w13_p9.json
2c1ea5015ba377cf3b505639f7d72664f479958642e38f5e69ef52d9cae19fff  jis/data/cells_check/dfs_w9_p0.json
a7e59246be4febd1a4b31d5bcf3388b50de78e609b61c837a488c74a29fc683e  jis/data/cells_check/dfs_w9_p1.json
3744bdbef8a71994967cae6cff12dc2e3d48751993fa81511296e0e461ee5b18  jis/data/cells_check/dfs_w9_p2.json
1c35daf3267a6c3b6fa3b730c6503e2978bef2be85c671d4f9ab051df81d36a7  jis/data/cells_check/dfs_w9_p3.json
831086c9890209a36396bf533fa1d42976639538dcbb0166c7da47a3804b7bcd  jis/data/cells_check/dfs_w9_p4.json
5c95fb98e3859e7aa21e3d719b23455efd2144770a8c8d33b9c9108a2d92c916  jis/data/cells_check/dfs_w9_p5.json
2fa2b716073c84a154a43c6666e308723a28819f43d9406a8e0ed35a776029e7  jis/data/cells_check/dfs_w9_p6.json
a250256f8e5dd1b084040956c17733a5fd825e9e6a602fb2a5d8364b1de6938e  jis/data/cells_check/dfs_w9_p7.json
17bac854c6f1e0d9f46356cf39326d3195f7cc06771efdb9b96edab984d0194d  jis/data/cells_check/dfs_w9_p8.json
291c67212f624da7a5526840f5a19b3cd9ae61467a9a86ca95d9ddf9fe882f91  jis/data/cells_check/dfs_w9_p9.json
# R8 six rows, part (b)
18f73a9d94ab2b444e1226ae361e3d065c2f54e3b199e8034a3587306712df89  jis/data/six_row_sat_w15_A.json
09ea34707bc3dabefc344fe3d4ca43c88794a7b5d1deefce71fc319f015e45e7  jis/data/six_row_sat_w15_B.json
78989302856ecd027042b4be1ab98896c3f4b5e3facd5cf38117e1b1c48d0b69  jis/data/six_row_sat_w16_A.json
c4720f085a30c9ff8c50e5cfc2d476d2110b1d5453937f5d3ffbfd334143379f  jis/data/six_row_sat_w16_B.json
a50a814b91ec70b84b72cb858b823b063e547109fc8f2b4e3f392afa73b42407  jis/data/six_row_sat_w17_A.json
134e902bfe3271d90528d53bf6b47176a69f7afa89279f378b8a2ceeceb1ec40  jis/data/six_row_sat_w17_B.json
042d7bb84ace19a290a90d882286810edc70bab64c666e261097e30fc3c318b0  jis/data/six_row_witness_brute_w15_17.json
# R9 small grids
54437aa701d02e64d45acb334af91f48ce9e61ed3269de7712ea595e2a8d0d61  jis/data/small_cells_sat_5x6.json
2bf6dc617c4df5ab7ab44b00c25522f340cb3708d5c6bafb2ee8824f5ba57b19  jis/data/small_cells_sat_5x7_b12.json
8ae88b1fef56c7aa06453305a599c32287dc6aca5315d6fcd70ff033bbc5c3c1  jis/data/small_cells_sat_6x6.json
ad0328bc888db581b53eadaf8e7649b37fb1fd85bd36236224305bbebedb0352  jis/data/small_cells_sat_6x7.json
127607e40636a2db6aa107a1ac4eb4e926c11c273fb8291fe970b59b3d339c6a  jis/data/small_cells_sat_6x8.json
13f749271c842ecd13c84ce30ea34bbfe10e92096ee9502874b1c32027dcbcc8  jis/data/small_cells_sat_6x8_b16.json
74224c9d69b066f45b4cd109da4aaca5517a6bc23cfbe310a3323a8cc85beb28  jis/data/small_cells_sat_6x8_b17.json
ad98b2b2773716ea7f44b0f6615da82202e9c274be38c292cbeb27b6035be3cf  jis/data/small_cells_sat_7x7.json
4eebdfe61648f67d2683e409406e6f812fa25f7ff8e5f80a78f3aaf0c6b6e6ae  jis/data/small_cells_sat_7x7_b16.json
18dea077a664353a9b2e40bbd268a743a5503a56e5a6a411eba28d4748d7faae  jis/data/small_cells_split_7x7_b15_case1_A.json
4185159ac588ed51ab6e4f1ba9895046a8505560d8cf0333295786aaa38e61e6  jis/data/small_cells_split_7x7_b15_case1_B.json
0abc40d59b9bc02951c1476c9b8acd6d38683b88acc4244db21fa30485cff1f3  jis/data/small_cells_split_7x7_b15_case2_A.json
d9004feb29950a2b319881114055da97f66fb67fe9368a03ae9881e8184bc79d  jis/data/small_cells_split_7x7_b15_case2_B.json
f7c161bfe7ba62ae9e1137344bdcc17c415d856d960de9a295a942ccd3a273b7  jis/data/small_cells_split_7x7_b15_case3_A.json
59bd6708a6937922c6ac64609aa81136f0ec3ed73a69555f4fb3feb791821a29  jis/data/small_cells_split_7x7_b15_case3_B.json
24c1c4e1274da24d28b1859868f3a6e647bef922173023511bc6d1669a69ac6d  jis/data/small_cells_split_7x7_b15_case4_A.json
f577e7929e400be8643a64680d9e675012624fe6873d8e3c14006c8981c42359  jis/data/small_cells_split_7x7_b15_case4_B.json
69576aea591fe44f2de0711319b5636fe8ed0a4cd78ec91f0ba432f7bf06c072  jis/data/small_cells_split_7x7_b15_case5_A.json
78d85135d479c13a64a84dc26c2e73c8b80f21862c03edce698087446a2d0377  jis/data/small_cells_split_7x7_b15_case5_B.json
84016d445a264955bf53d968985a5ef61ce070ad9c327e192fbc808eedd8ee6e  jis/data/small_cells_split_7x7_b15_case6_A.json
00dcbe52d65739361d7374c1e7c26c5cd74f36cac3767bf364f47f3bb6ee6bc7  jis/data/small_cells_split_7x7_b15_case6_B.json
6b96a8038caf7d0c6c8fca914380575877b6b012a22d844a1e943d69a43a5795  jis/data/small_cells_split_7x7_b15_case7_A.json
47a90443555785bd1098a721b669e34240a6e9a6400f81d83707dee164d96c99  jis/data/small_cells_split_7x7_b15_case7_B.json
c528a5a42b3711baede792038852dcf88ca3f0c598ac88e02e00c10ba4685140  jis/data/small_cells_ilp_highs.json
8285d1dd08fe54402ea06056dc5d58bd4eb3b80c33b8a62f8f43814e51c9b14e  jis/data/small_cells_ilp_cbc.json
789599c9d7f31c1944fd322524d10d7193bf73c779ef54e44adf48e9d58cfbf2  jis/data/cells_check/sat_jobs.json
c3f59ec3c76e025b589645509716a1ec612a98c14635c47539df504b526887a5  jis/data/cells_check/sat_jobs_summary.json
2a3cd02c0a629079d1628556ed93a7c42d25779b91567913cdfc76268214a86b  jis/data/cells_check/sat_jobs_satcases.json
0ae43132b78b064c8a73f246146ee0017534cdb66bcfc0f2a0b8be134b6f408d  jis/data/cells_check/sat_jobs_satcases_summary.json
2bd14377c19245e21c7b0dade7867d9c59fac8f43836fd7a8fd7e5c24d3c3f5e  jis/data/cells_check/sat_4x6_b10_maplechrono.json
1d0a0f444e3fa25784d48aeb156f5abf091c249fc04d908a622d4989ce4ad323  jis/data/cells_check/sat_4x6_b11_maplechrono.json
e5400885d55a05396cb6961a8fe46f342ae6dc90faf224ddd1e9a9a846ed5aaf  jis/data/cells_check/sat_5x6_b11_cadical195.json
167e5623136fe5acd477979c452dbeb5b5c8458ba020b3033ac3f264571efaef  jis/data/cells_check/sat_5x6_b12_cadical195.json
c33fef9716eece1a5ac59ec3404110ffb2b7312202345a1cf5c0533c01479d2f  jis/data/cells_check/sat_5x6_b12_glucose42_row3.json
a1311278e87f3e84e7409a786a5a575b7c9bd9cba37c66b46cb33cb38846a220  jis/data/cells_check/sat_6x10_b17_cadical195.json
bcceb3efa2ef37d06a7cd7ef02b300dd90ea38900021e9c5f2834ec78b27116f  jis/data/cells_check/sat_6x7_b13_cadical195.json
583bdede58aa93235f141504c0ff40ce5379bde0364235b226ff3cee74f44f77  jis/data/cells_check/sat_6x7_b13_glucose42_row1.json
c2eb31d815667f802cb5388fc6962e84dcb40dba4c00c05c6857186975f76a46  jis/data/cells_check/sat_6x7_b13_glucose42_row2.json
866e738d8d480056dbab4696966a116beda943a13339f3642a6f9b181621ed7c  jis/data/cells_check/sat_6x7_b13_glucose42_row3.json
f465d6eab5971f24a7481a080f03254d22323556985eefb2b3d425a6e88543ea  jis/data/cells_check/sat_6x7_b13_glucose42_row4.json
5b25e644a271bd077ced71f8149de4cff9ce9dbcfcdd016c9b1788ee2dccdf32  jis/data/cells_check/sat_6x7_b13_glucose42_row5.json
14a735a7f68f4665edbb8d11ce87a1ef381f854ac2e7a449f60fdbf44e56d9a8  jis/data/cells_check/sat_6x7_b13_glucose42_row6.json
25c8bcd3e8851922ece9c227f82807a57418e891ffff886e6703fee0836181de  jis/data/cells_check/sat_6x7_b14_cadical195.json
015f87a941723af6a8e85697e21caf09628803b07213e0a635645a100034bdd5  jis/data/cells_check/sat_6x7_b14_glucose42_row1.json
69effa333434e08d044bc35a89a04764baa82ff93e07a8fb9a7cf337f3b7f89c  jis/data/cells_check/sat_6x7_b14_glucose42_row2.json
fd3882f157cfdaac69fd72a80de89900077c1bb97a3f76cb6e8cafbec32d5b96  jis/data/cells_check/sat_6x7_b14_glucose42_row3.json
75ab533133727699096416cee1d4f0c5a51de02f1c7553cbc09a937f1a20b9dd  jis/data/cells_check/sat_6x7_b14_glucose42_row4.json
e88f3c7dfcca21c3bb1de2cb6be1fd90eea1df9dfd708928e5de1194705942b7  jis/data/cells_check/sat_6x7_b14_glucose42_row5.json
88111f6087112b439ede78a2cff30caca4f1d10b07c20ac1985aadc9e5e3b83d  jis/data/cells_check/sat_6x7_b14_glucose42_row6.json
09e8600eaf172fd331c59688a35ee366bad8f577f64f744d5e5e68c902875071  jis/data/cells_check/sat_6x7_b14_lingeling.json
08ec3178aee0c563d1d32fa3c4fe363589f075544c901f97eccab9fc65748e69  jis/data/cells_check/sat_6x8_b15_cadical195.json
c88079736c03b70dd53c271120e4216f12229f1af9a7f709a8e0733ee2134d22  jis/data/cells_check/sat_6x8_b15_glucose42_row1.json
b59fddd94714118b6d365fdd9c59815a0900446246d0266c4ff8acce8d75234f  jis/data/cells_check/sat_6x8_b15_glucose42_row2.json
b73a7be9977d0f18ccbd96d173a152aa31dda0727201119d9e66d7d170a15e3f  jis/data/cells_check/sat_6x8_b15_glucose42_row3.json
e651a8836465620975d827e5e89e74dacd3c2c9f150bb5a1ffb1af5d8908d395  jis/data/cells_check/sat_6x8_b15_glucose42_row4.json
338ac8f420aa572d80302d3b5f6e65061bd418415b0878be28f035740df30163  jis/data/cells_check/sat_6x8_b15_glucose42_row5.json
96dd19e6b28f7ef571f8dc8f2f5d6766dc10298466e7c12b2860587ebf8c9831  jis/data/cells_check/sat_6x8_b15_glucose42_row6.json
d7435937460dc3025599666f64f82e2f8aa62d83aacf5ead4aba6c5308a5f349  jis/data/cells_check/sat_6x8_b16_cadical195.json
bc0bc04271749873b62bca942d516a65ccd5c1e81f0f4ef4145b42e06c95eca4  jis/data/cells_check/sat_6x8_b16_glucose42_row1.json
8472053eb3a1ddc7f9d4063d21eebff8245505592eb0c2552a925156a214fee5  jis/data/cells_check/sat_6x8_b16_glucose42_row2.json
578316b9d8b28671189087846aa95e262ef4fc72442259282074c55f63f319e2  jis/data/cells_check/sat_6x8_b16_glucose42_row3.json
e22e10877929443b709ef4f2ab9a6cccef30b1acf7473dd7e1fe78511e2bb17e  jis/data/cells_check/sat_6x8_b16_glucose42_row4.json
1acfe9c26f64afa0372c21adb3ab551d1466199e28bf4a07bbabebd37f53cb02  jis/data/cells_check/sat_6x8_b16_glucose42_row5.json
54ce081f256eb418c23a20b9d8c7fc830067f9fb0fee5dba1f89e8384c3d3a57  jis/data/cells_check/sat_6x8_b16_glucose42_row6.json
e11e2ef127ca906288ec593985893140f20c43fda978dd037836d2e44688c642  jis/data/cells_check/sat_6x8_b17_maplechrono.json
f842b98deabefc3a79c099b4e9b50742847736b742255de5b9575b6801d4542e  jis/data/cells_check/sat_6x9_b16_cadical195.json
97e946e0b698d453d55a24cbfdc1319b75ae5258ff27a2c0582ef255a2dcb4ae  jis/data/cells_check/sat_7x7_b14_cadical195.json
5c348bb3c5928c96fe443d47e1c26757cf0f18edad3e9f5fc3ff2fb1c834fc5d  jis/data/cells_check/sat_7x7_b14_glucose42_row1.json
c601149b09fe25b6dae6e36487f1cacf0520cee2f2fca58ecc9f957276edc911  jis/data/cells_check/sat_7x7_b14_glucose42_row2.json
4798a56148fbd85e5c66a74aebe761eb4b75f85eaba6896c365fe53d174dcf33  jis/data/cells_check/sat_7x7_b14_glucose42_row3.json
2bbdf4aeae73de3f330ffa2d4f609a3279c3dcf1369232fe11704ba59f275ee6  jis/data/cells_check/sat_7x7_b14_glucose42_row4.json
7ffabcfc3633591662b9a6a25d08d5da7ae988642fcd7c32ad07eb2efb8c5cdf  jis/data/cells_check/sat_7x7_b14_glucose42_row5.json
aaddf7c25836b1762696f3b5bf172b706df5e176acbbcd84517868ac9c9f735c  jis/data/cells_check/sat_7x7_b14_glucose42_row6.json
ea9923deb23ea6d1b652c6480e47a6f74e35410380c41e785ecba9f9e2e1846d  jis/data/cells_check/sat_7x7_b14_glucose42_row7.json
255b1f776f5533d465501b5f5bbe1dfdce9bcbb75f780912f8aa5f02c35ac7d7  jis/data/cells_check/sat_7x7_b15_cadical195.json
9a7fb8570a5d9bdac1df6dec0b18959cd3073f015b1a6b6227a8560232bb9967  jis/data/cells_check/sat_7x7_b15_glucose42_row1.json
a3de5a6192340ca2fc34f7f94bb46070e9dfed2e70123887b7a8b458dd12e3b6  jis/data/cells_check/sat_7x7_b15_glucose42_row2.json
47cece9a95bc3b6b6ad19b7bb20a765923c61be08d0c21ed3ab03f576d0d9287  jis/data/cells_check/sat_7x7_b15_glucose42_row3.json
a6b0f632ad9af7789554464c247d6ba90bc805085ba46b8f9dbe9efcbb8fcf0a  jis/data/cells_check/sat_7x7_b15_glucose42_row4.json
406797cd4e7e69885a24502e6072ef2b607f1f8abb78ca5ab3ebe1a02addd7b1  jis/data/cells_check/sat_7x7_b15_glucose42_row5.json
d01e2a9344175975f3d1180c9e81652f0e1a60814b271ad1db711b25e546f663  jis/data/cells_check/sat_7x7_b15_glucose42_row6.json
feec5fac100d8730c9881138d5d27cba3a0fc1f4bd7f6a926be71efbbca5f124  jis/data/cells_check/sat_7x7_b15_glucose42_row7.json
16b739ea6e7db914539dff3469d55c6b9c877f359d5c4bee2a8cea19024df726  jis/data/cells_check/sat_7x7_b16_maplechrono.json
3e0ffd15599bf8e86069aee8396c1d30f11df71f99be207ee7255a11f5cf8768  jis/data/cells_witness_check.json
# R10 table counts and f(7,8)
ec560b775682eb346f4e36d6319978779bcba6c9f143ee247fe076d4e952f68b  jis/data/table_counts/sat2_5x7_12.json
e989e9f8cca8bbb44b0d80a30595c0ccba918f7c66aa549d7cd77d6328c9920d  jis/data/table_counts/sat2_6x6_12.json
d52f02ef4b717c1f5df2f5e02da34002140da1712f2922d626abe541e53acfbd  jis/data/table_counts/sat2_6x7_13.json
c136c2550ac3ef957526817d0023c7274454b1673c9ac9f5dde1b77eefdd938e  jis/data/table_counts/sat2_6x8_15.json
5f51f0689adbab5bd4669c55a6a582ea9dc779ca7e980035bbc05b9bac083890  jis/data/table_counts/sat2_7x7_14.json
a226c5386516208142994a68421475d7b9a7aac323d7941dfce03c581a56121a  jis/data/table_counts/sat2_7x8_15.json
c6c64a4cb852660cb418ff2ced1521d4813da2444d5d2357f0a6cd48ddbdbe3d  jis/data/table_counts/sat2_7x8_16.json
2e94b1d2d1069c0e28e85ca0ffdd6e40c63cdcb33e244e9ccd3b348b8b34e178  jis/data/table_counts/sat2_7x8_17.json
6cdef8f90d5b97fb308e18cba07a14276a436f614a0d6637d5df9723ca106434  jis/data/table_counts/sat2_digests.json
b1616186d90e01ddedfff6324be9578a0a57cdbdee56167581cc968f3090d25b  jis/data/table_counts/sat2split_7x7.json
c4717fb24e4116016ee622a637a2948c8536ee2f236677e3229c1b8d2475a028  jis/data/table_counts/sat2split_7x8_16.json
287b3d74ed8f35ecf1a12551c3444660868b79e339f9d0c91504047954da2b09  jis/data/table_counts/sat2split_7x8_17.json
d863eb201e9577c208d7ca001f5eaa5a85e475b1670e83635cf349701165a456  jis/data/table_counts/sat_5x6_11.json
5c56cefa0669a06aac8a89cf2748405c3831eba863d07dabe54c2802bc988501  jis/data/table_counts/sat_5x7_12.json
d37c1ba7616e6926426c8b981b305771d7fc9e4ed5a08f45c600335ed643e1ac  jis/data/table_counts/sat_6x6_12.json
8f3210e4b3dda73a30784143fccd572e79303d1c573697b20b0543914759d0b1  jis/data/table_counts/sat_6x7_13.json
1a4ea1d1aad523dab35b96b9f80e059ea3299cdaeed3e3be550ec3ee562f0c9d  jis/data/table_counts/sat_6x8_15.json
58733d21bfdd1376fe831bb16d9f776cd6bcda44cd7e7ff01a7bddea276f20c4  jis/data/table_counts/sat_7x7_14.json
22905ade12236f062e402c4abcc0f9a616e221a0841ed8fd0c74eb245b07d7d0  jis/data/table_counts/sat_7x8_15.json
9042e70ccf94217236e61e8a0801c75ebcb3ac1ab3b6050ee332056c941b5ce4  jis/data/table_counts/sat_7x8_16.json
3a601bfcc5fd29214a176f24bed4c4b7f25e6232d34630f73ef58a66d3394a86  jis/data/table_counts/sat_7x8_17.json
a43042451170fde1cf92ef938c7e096c6d692e2c143bb33fc6a5618817f88404  jis/data/table_counts/sat_digests.json
dfcec052e3b8d8a043320554d6e5f5cc0eb4eebabe0cb502c1306b04276a1c3d  jis/data/table_counts/satsplit_7x7.json
ab5999a864956d8e82bf53c2f9153214bad1cab9c9906c682bc375fe382b15c6  jis/data/table_counts/satsplit_7x8_17.json
e22b46fb0eb242ab0fab9fd0fd875107357528147e1fae316c1cddd35cb62acd  jis/data/table_counts/search2_7x7.json
39b99a81c34e5eb51e134a857b9cf0cbe00f80246815d3a8aa58260306a2f943  jis/data/table_counts/search_5x6_11.json
9ec5d26a8ac5c99451dc6ce10d8828910c91b9aed93b82fe810b18ff2ec7bb4a  jis/data/table_counts/search_5x7_12.json
b8339e0d0ecf04fef6df12c743e6ddd411d51bd8a203e9ec00722142210a696e  jis/data/table_counts/search_6x6_12.json
76e50eaff65edc5c3cd52f79164acee3fce7556c9249f0f8968f871e877fa6bd  jis/data/table_counts/search_6x7_13.json
0f2d70a30f51289145faf71052ae9b404a9452cf0a278ccaae9657b7ae29e294  jis/data/table_counts/search_6x8.json
5eda4a213a5ae2ebbce9e65db4288c0cf39c8fa840ff56ce2dcb6fb6499a6ef9  jis/data/table_counts/search_6x8_15.json
a294c3eed170d7336d301f4b61a7d6aa6925b2fe8f70f03c39739fb3136f2b90  jis/data/table_counts/search_7x7.json
535ebe41e3dc6b46008543a87d049bd7e9166db8733536276cb87b93de12f218  jis/data/table_counts/search_7x7_14.json
81c89679a87a2617e7b61e000a98d82436688d577f62e6fa26dade7c73eeace8  jis/data/table_counts/search_7x8_15.json
283c30ef79ad1eb07e9a2940fc6516dcba9fdc8ca25a846f509902322ff28d7a  jis/data/table_counts/search_7x8_16.json
685b1e4f12cc36db1f8186310c3cf8116aa4d2c8811966addef3be4d55cfeb67  jis/data/table_counts/summary.json
# R11 six rows, widths 9 to 14 (open question)
16ba1a42645985cb24dd1b9b96426a783fa46ef8cc0a76516cb49a56210eeea3  jis/data/small_cells_sat_6x9_b16.json
fe4a52c99a67bedb0c3f3176f8f21d2af76b3660f3b8e954382fc572cd346cef  jis/data/six_row_collar_6x9_check.json
```
