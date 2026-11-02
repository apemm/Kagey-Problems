# Paper D v1 source verification

The verified source commit is
`7e78cbad17b2dc60101363d09275e0ee5067c4d5`. The release tag
`paperD-arxiv-v1` targets this commit. This record and the post-commit logs are
stored in a later evidence-only commit; they do not change the tagged sources.

Both release checks passed at the source commit:

- `lake build PaperD` exited with code 0. See `release-lean-build.txt` and
  `release-lean-exit-code.txt`.
- `verify_all.py --paper d` exited with code 0 in a separate Git export of that
  commit. All six scripts passed. See `release-numerical-verification.json` and
  `release-numerical-verification.txt`.

The numerical suite checks the archived threshold records and runs three fresh
short probes. It does not rerun all nine full threshold jobs. The 14 reviewed
threshold source and data files remain byte-identical to commit
`b3fe9977af42c87aa0b627e736d2d34c7befe696`.

The full axiom audit, recorded in `verification-manifest.json`, covers 353 modules
and 23,777 theorem/lemma declarations. Only `propext`, `Classical.choice` and
`Quot.sound` occur. A final run of `check_final_state.py` confirmed that all 353
audited source hashes still match, all release references use the tag, and the
existing disclosure is unchanged. The scope and explicit mathematical inputs
of the formalization are documented in `README.md`.

The tagged source includes the rebuilt journal and extended PDFs, their source
archives, and the metadata. Their final package checks are recorded in
`../paperD-audit-2026-11-01/pdf-checks.json` and
`../paperD-audit-2026-11-01/delivery-manifest.json`.
