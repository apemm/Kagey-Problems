# Paper D verification records

The recorded audit checks 386 modules and 24,005 theorem or lemma declarations.
Its allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
`verification-manifest.json` contains the imported-source inventory, hashes,
toolchain versions and declaration results. `build-log.txt` contains the run output.
These records are preserved from the completed audit, not a new execution.

The [coverage map](../../lean/PaperD/MAP.md) specifies the hypotheses and limits
of each formal result. The transcendental interval enclosures are checked by
the numerical scripts, not by Lean.

To repeat the audit, run the wrapper with a Lake workspace outside OneDrive
or another synchronized folder.

```text
python kagey-problems/problem131/paperD/verification/run_verification.py --workspace C:/Users/arjun/lean-work/paperD
```

The [Paper D README](../README.md) lists the certificate scripts and numerical
records. `delivery-manifest.json` records the manuscript sources and package hashes.
The manuscript and packages are built with `../build_submission.py`.
