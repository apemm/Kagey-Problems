# PaperF recorded in the verification log (2026-10-25)

- `verify_lean.py`: added `PaperF` to `LIBS`. Default workspace `~/lean-work/{name}` resolves to `~/lean-work/paperF`, whose lakefile already has `srcDir` set to the repository's `lean` folder, so no copying was needed.
- Ran `py -B verify_lean.py PaperF` (the script merges into the existing files). Result: 20 modules, 252 theorem/lemma declarations, 36 build warnings, axioms within propext, Classical.choice, Quot.sound; parsed declarations equal the theorems Lean finds.
- `build-log.txt` now has a PaperF section; `verification-manifest.json` has PaperF, with PaperA to PaperAD kept (1257, 307, 715, 23503, 4). Total declarations 26038, all checks passed.
- `README.md`: counts unchanged (20 modules, 252); added a sentence that the script records PaperF. `PaperF/MAP.md`: replaced the sentence saying the script does not cover PaperF.
- Backups of the earlier log and manifest: `~/lean-work/log.bak`, `~/lean-work/manifest.bak`. Run output: `~/lean-work/verify-paperF-record.log`.
