"""Run the complete Paper D build and declaration/axiom audit for this revision."""
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
