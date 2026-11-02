"""Run the existing full Paper D verifier, saving this revision's evidence here.

From the repository root:
  python reports/paperD-formalization-2026-11-01/run_verification.py --workspace <cache>

The existing verifier checks the root import closure, builds every imported
module, compares source declarations with Lean's declaration inventory, and
prints the axioms of every theorem. It rejects proof admissions and reports
unimported source files. Mathlib and unchanged proof objects may be reused from the cache.
"""
from pathlib import Path
import importlib.util
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / 'kagey-problems/problem131/lean/verify_lean.py'
spec = importlib.util.spec_from_file_location('paperd_verifier', SOURCE)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
verifier.LOG_FILE = HERE / 'build-log.txt'
verifier.MANIFEST_FILE = HERE / 'verification-manifest.json'
sys.argv = [str(SOURCE), 'PaperD', *sys.argv[1:]]
raise SystemExit(verifier.main())
