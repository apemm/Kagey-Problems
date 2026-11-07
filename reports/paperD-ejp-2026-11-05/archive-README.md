# Verification archive for Paper D

This archive contains the Paper D Lean library, its pinned Mathlib dependency,
certificate scripts and records, the phase-figure script and data, and the
November 6, 2026 verification audit. It accompanies repository tag
`paperD-ejp-v2` at https://github.com/apemm/Kagey-Problems.

Extract it outside OneDrive or another synchronized folder. With the matching
Lean toolchain installed, run from `lean/`:

```text
lake exe cache get
lake build PaperD
```

The full declaration audit can also be run with `verify_lean.py PaperD`, giving
that script an explicit `--workspace` pointing to the extracted `lean` folder.
The archived `audit/run_verification.py` is the repository wrapper and assumes
the original repository layout; use `lean/verify_lean.py` in this archive.

For the short independent numerical check, install python-flint 0.9.0 and run
`python -O check_critical_shape.py` from `paperD/`. Historical numerical records
state their own versions, arguments and precision. Re-running a certificate
updates its local output file, so compare with the archived record separately.

The phase illustration uses NumPy, SciPy and Matplotlib; its cached data are in
`paperD/data/limit_phase_illustration.npz`. It is not a certificate. The full
parameter sweep is not needed to reproduce the short endpoint/slope check.

Read `audit/proof-review.md` and `lean/PaperD/MAP.md` for the distinction between
kernel-checked deductions, explicit classical inputs and written/numerical
proofs. No Zenodo DOI has been assigned by this archive.
