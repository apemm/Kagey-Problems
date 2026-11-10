# Problem 001 research archive

Working notes, proofs, audits, checker scripts and small certificates for Problem 001,
from 7 to 10 November 2026. These are research notes. They have not been refereed, and
some statements are superseded by later notes in the same archive. The manuscript in
`../jis/` is the reference for published claims.

## Where to start

| File | Contents |
|---|---|
| `2026-11-09/full_problem_push/REPORT.md` | Consolidated results table with links to every proof note |
| `2026-11-09/CLAIM_LEDGER.md` | One row per claim: exact statement, dependencies, audit status |
| `2026-11-09/AUDIT_threshold_upper_bound.md` | Independent audit of the equality-threshold upper bound |
| `2026-11-09/small_boards/` | Width table, bounds on m_0(8) and m_0(9), and structure of the small equality boards |
| `2026-11-09/LITERATURE_right_angles.md` | Literature on girth-eight graphs, right angles in grids, and related problems |
| `2026-11-10/squares_sidon_lower_bound.md` | Why structured hosts and alteration stop at exponent 6/5 on squares |
| `2026-11-09/quadratic_gap_structure.md` | Structural results on the remaining quadratic gap |
| `2026-11-08/REPORT.md` | Construction obstructions, sea entropy, square bound |
| `2026-11-07/REPORT.md`, `2026-11-07/REPORT_1xh_construction.md` | The `1, x, h` family and its three-corner law |

## Layout

* `2026-11-07/`: the `1, x, h` construction, scripts, and verified boards at heights 11, 15, 19.
* `2026-11-08/`: obstruction notes, `counting_followup/`, `general_dominance_quadratic/`.
* `2026-11-09/`: top-level notes, `odd_graph_entropy_square/`, `small_boards/`, and `full_problem_push/`.
* `2026-11-10/`: square-board notes and experiments.

## What is not here

Files over 1 MB other than notes and scripts are left out, as are binary state files
(sea-graph checkpoints, Perron weights, packed state lists, about 38 GB in total), logs,
and the bundled solver runtime. The scripts that produce those files are included. The
omitted large certificates are named in the notes that cite them.
