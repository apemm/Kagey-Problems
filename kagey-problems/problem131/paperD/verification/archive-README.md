# Verification archive for Paper D

This archive contains the Paper D Lean library, its pinned Mathlib dependency,
certificate scripts and records, and the phase-figure script and data.
It accompanies repository tag `paperD-ejp-v9` at
https://github.com/apemm/Kagey-Problems.

Extract outside OneDrive or another synchronized folder. With the matching
Lean toolchain installed, run from `lean/`.

```text
lake exe cache get
lake build PaperD
python verify_lean.py PaperD --workspace .
```

The completed declaration audit is in `paperD/verification/verification-manifest.json`
and `paperD/verification/build-log.txt`. The coverage map in `lean/PaperD/MAP.md`
distinguishes kernel-checked deductions, explicit hypotheses and written proofs.

For the independent numerical check, install python-flint 0.9.0 and run
`python -O check_critical_shape.py` from `paperD/`. Numerical records state
their versions, arguments and precision. A certificate rerun updates its local
output file, so compare it with the archived record separately.

The phase illustration uses NumPy, SciPy and Matplotlib. Its cached data are
in `paperD/data/limit_phase_illustration.npz`. It is not a certificate.
