# Data

Results of the scripts in `../scripts`, as JSON (and a few run logs). Coordinates are one-based
(column, row) with (1,1) the top-left point, as in the paper.

Files larger than 2 MB are stored gzipped (`name.json.gz`). Unzip them with `gunzip -k name.json.gz`
before rerunning a check script that reads them. The scripts write the uncompressed files again
when they are rerun.
