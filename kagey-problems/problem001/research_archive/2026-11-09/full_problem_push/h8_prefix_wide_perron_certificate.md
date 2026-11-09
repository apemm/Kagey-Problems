# Exact Perron certificate for the height-eight prefix

9 November 2026. The induced processed-prefix graph has a recurrent
component with 2,393,411 states and 5,044,803 internal labeled edges.
Its exact Perron enclosure is
\[
\frac{2{,}591{,}155}{10^6}
\le \rho(A)\le
\frac{2{,}591{,}156}{10^6}.
\]
This is an enclosure for this induced component, not an upper bound
for the full height-eight sea graph.

The component has ID 8028601 in
`sea_sparse_h8_processed_prefix.bin.components`. Its membership and
strong connectivity were independently checked by Tarjan and Kosaraju.
It contains the constant-row states for rows two through seven, so the
adjacent-row bridge identifies it with a subgraph of the canonical
component. Consequently
\[
\lambda_*(8)\ge2.591155.
\]
The complete height-eight graph and its component dominance remain
unresolved.

`SeaPerronWide.cs` compresses the chosen component, performs power
iteration on \(A+I\), and rounds the positive vector at scale
\(10^{60}\). It then derives rational bounds using exact `BigInteger`
inequalities. The smallest saved weight is
\[
102031568509576323222220498052687071281152.
\]
Thus the small coordinates that defeated the earlier \(10^{12}\)
rounding are retained.

`SeaPerronWideCheck.cs` independently reads the original graph rows.
It checks that the saved vertex IDs are exactly the reported component,
that every weight is positive, and that every row satisfies
\[
2{,}591{,}155\,w_i
\le 10^6\sum_j A_{ij}w_j
\le2{,}591{,}156\,w_i.
\]
The checker does not reuse the compressed power-iteration graph.
All 2,393,411 rows passed. The two source files also passed an
independent code audit.

Run `run_sea_perron_wide.ps1 -OutputTag perron_wide_recheck` to reproduce
the calculation under a fresh output name. It deliberately refuses to
overwrite an existing weight file. The saved certificate and check are
`sea_sparse_h8_processed_prefix.perron_wide.8028601.json` and
`sea_sparse_h8_processed_prefix.perron_wide.8028601.check.json`.
The weight file has SHA256
`fb002a9f990dbe084565758e5df44c8013b5342a0c71ace355c2b53686c2351c`.

## Frozen-state continuation audit

The separate `SeaFrozenStorage.cs` and `build_frozen_sea.py` sources
passed independent review. Lookup never interns a new state or block;
hash matches are checked against complete decoded state contents.
The residual transition and hash routines are copied unchanged.
Rows are flushed before the status file atomically advances its
committed cursor. Resume verifies the checkpoint and residual hashes
and truncates any uncommitted output suffix. If a continuation ends
before every frozen state is processed, its certificate must use the
induced graph on the processed source IDs, dropping outgoing edges to
the still-unprocessed frontier.
