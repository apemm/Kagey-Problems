# Scripts for the computer-assisted results

Every file here is a Python script. All of them run on Python 3.14.3. The SAT solvers come from
pysat 1.9.dev15 (CaDiCaL 1.5.3 and 1.9.5, Glucose 3, 4 and 4.2, MiniSat 2.2, MapleChrono and
Lingeling). The algebra uses SymPy 1.14. The results go to `jis/data`.

The scripts read their inputs from `jis/data` by paths relative to this folder. The three
four-row machines are in `jis/data/four_row_machines`, and the three-row reference tables that
some three-row checks compare against are in `jis/data/three_row_reference`.

The table lists the scripts behind each computer-assisted result in the paper, with the longest
single run of each group. Section, theorem and remark numbers refer to the paper `pemmasani.tex`.

| Result | Scripts | Longest run |
|---|---|---|
| Section 5 (three rows) | `three_row_closed_form`, `three_row_closed_form_check` (SymPy identity and exact fractions to m = 100) | 4 s |
| Section 5 (three rows) | `three_row_definition_check`, `three_row_orbits`, `three_row_symmetry_check` (counts and orbits from the definition) | 55 s |
| Section 6 (four rows) | `four_row_counts`, `four_row_dp_check` (two counts on the machines to m = 1500) | 6 s |
| Section 6 (four rows) | `four_row_direct`, `four_row_direct_check` (every equality candidate) | 84 s |
| Section 6 (four rows) | `four_row_equivalence_check` (the automaton of Lemma "six columns of memory", built from the definition, accepts the same words as the machines) | 89 s |
| Section 6 (four rows) | `four_row_recurrence`, `four_row_recurrence_check`, `four_row_window_check`, `four_row_rho_check`, `four_row_root_isolation` (certificates and growth) | 48 s |
| Five rows, widths 6 and 7 (Theorem "five rows", part (a)) | `five_row_structured_sat`, `five_row_column_sat`, `five_row_unstructured_sat`, `five_row_sat_check` (four SAT encodings) | 14 s |
| Five rows, widths 6 and 7 (Theorem "five rows", part (a)) | `five_row_unstructured_dfs_check` (column search) | 431 s |
| Five rows, every width from 8 and the four 5 x 8 optima (parts (b) and (c)) | `five_row_collar_family`, `five_row_family_brute_check`, `five_row_geometry_check` (three rectangle enumerators on the collar test board) | 35 s |
| Five rows, the four 5 x 8 optima (part (c)) | `five_row_width8_candidates` (all 5,040,000 equality candidates) | 145 s |
| Five-row counts (Remark "five-row counts") | counting runs of the SAT scripts above, and `five_row_count_dfs_check` (column search) | 854 s |
| Five-row counts (Remark "five-row counts") | `five_row_optima_dp`, `row_bound_count_dp` (two transfer counters) | 185 s per width |
| Six rows (Theorem "six rows") | `six_row_structured_sat`, `six_row_sat_check` (three encoders) | 606 s |
| Six rows (Theorem "six rows") | `six_row_dfs_check` (column search) | 948 s |
| Six rows (Theorem "six rows") | `six_row_witness_brute`, `six_row_collar_brute` (witness and collar test board from the definition) | 25 s |
| Six rows, widths 9 to 14 (open question 2) | `six_row_collar_6x9_check` (collar test boards of the three stored 6 x 9 witnesses, two enumerators; only run 0 passes) | 7 s |
| Small grids 6 x 6, 6 x 7, 7 x 7 and 6 x 8 (Theorem "the guess fails", part (a)) | `small_cells_sat`, `small_cells_split` (two encodings and a case split) | 1,578 s |
| Small grids (Theorem "the guess fails", part (a)) | `cells_sat_check` (third encoding, written from scratch) | 989 s |
| Small grids (Theorem "the guess fails", part (a)) | `cells_witness_check` (the stored witnesses) | |

The ILP program `solver/engine.py`, the brute-force check `solver/brute.py` and the verifier
`verify_narrow.py` live in the folder `kagey-problems/problem001` and are described in Section 9
of the paper.

## Other files

The other scripts in this folder are shared code, summaries and further checks made along the
way. The paper cites only the scripts in the table and the three programs above. The `verify21_*` scripts and
`five_row_w21_compare` recheck an earlier five-row witness of width 21. The paper no longer
needs it, since the width-8 blackout covers every width from 8 on.
