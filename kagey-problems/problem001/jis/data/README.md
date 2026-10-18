# Data

Results of the scripts in `../scripts`, as JSON (and a few run logs). Coordinates are one-based
(column, row) with (1,1) the top-left point, as in the paper.

Files larger than 2 MB are stored gzipped (`name.json.gz`). Unzip them with `gunzip -k name.json.gz`
before rerunning a check script that reads them. The scripts write the uncompressed files again
when they are rerun.

The folder `four_row_machines` holds the three four-row machines, one for each pair set, read by
`scripts/four_row_machines.py`. The folder `three_row_reference` holds the three-row transfer
matrix, its recurrence and counts, the class generating functions and the window tables that
`three_row_closed_form`, `three_row_closed_form_check`, `three_row_formula_check` and
`three_row_orbits` compare against.
