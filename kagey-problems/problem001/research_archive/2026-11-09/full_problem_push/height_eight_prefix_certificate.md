# A certified height-eight canonical lower bound

9 November 2026.

The parity sea's canonical component satisfies
\[
 \lambda_*(8)\ge 2.591155.
\]
This is an exact lower certificate from a finite induced subgraph.
The full height-eight sea graph is not complete or classified.

## Search and extraction

The sparse search stopped at its memory cap with 55,967,492 discovered
states and 20,360,000 fully processed source states. Its recorded memory
was 20,489.5 MiB and total elapsed time was 5,259.2 seconds, including
checkpoint output.

The processed-prefix extraction keeps exactly those source states and
all known transitions whose targets also lie in the prefix. It retains
38,582,941 labeled edges and removes 39,972,924 edges into the unprocessed
frontier. The graph's 20,360,000 states have one cyclic strongly connected
component, of size 2,393,411; all other components are acyclic singletons.

The cyclic component has ID 8,028,601 and contains the constant-row
fixed states for rows 2 through 7. The constant-row-one state is outside
the prefix. Nevertheless, the adjacent-row parity bridge theorem puts
all constant rows in the same component of the full graph. Thus this
finite component is contained in the full canonical component.

The two-pass SCC computation and a separate iterative Tarjan computation
agree on the complete component partition of all 20,360,000 states.
The independent check is recorded in
[sea_sparse_h8_processed_prefix.tarjan.json](sea_sparse_h8_processed_prefix.tarjan.json).

## Exact spectral certificate

Positive integer weights scaled to approximately \(10^{60}\) satisfy,
for every state \(i\) in the component,
\[
 2591155\,v_i
 \le 10^6\sum_{i\to j}v_j
 \le 2591156\,v_i.
\]
The sum counts labeled edges with multiplicity and uses only targets
in the same finite component. The independent checker reads the
original graph and component files, and verifies all 2,393,411 rows
and 5,044,803 internal labeled edges with arbitrary-precision integers.

Therefore the component's Perron root lies in
\([2.591155,2.591156]\). Extending its lower-certificate vector by zero
to the full canonical component proves the displayed lower bound.
The upper endpoint applies only to this finite component.

The earlier \(10^{12}\)-scale integer weights were too coarse because
some normalized eigenvector entries are about \(10^{-19}\).
Their weak enclosure is superseded by the wide-integer certificate.
The floating-point iteration only proposes weights; the reported
inequalities are checked exactly.

## Reproducible files

- Checkpoint: sea_sparse_h8.checkpoint.
- Extraction: sea_sparse_h8_processed_prefix.extraction.json.
- Graph and components: sea_sparse_h8_processed_prefix.bin and its
  .components file.
- SCC report: sea_sparse_h8_processed_prefix.json.
- Wide certificate and independent check:
  [certificate](sea_sparse_h8_processed_prefix.perron_wide.8028601.json)
  and [independent check](sea_sparse_h8_processed_prefix.perron_wide.8028601.check.json).

The checkpoint SHA-256 is
1e5de97f087e85cd711cb949bd19536ef89abd6855c95f9cba71fbe99565aa50.
The graph SHA-256 is
96d2ea9f79d6495f6602b9dc86fdd3b69d2edee83fd5932dcfb674f2bb912fb3.
The component file SHA-256 is
70d4cfabd8c1cb2e1e5fed8064f822b4221d8fa3165513e01cc1f5d0cafbf800.
The wide-weight file SHA-256 is
fb002a9f990dbe084565758e5df44c8013b5342a0c71ace355c2b53686c2351c.

A separate frozen-state continuation may strengthen this lower model by
computing more transitions among the already saved states. It preserves
this checkpoint and certificate. Even completing that finite state set
would not establish completeness of the full sea graph.
