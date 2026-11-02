"""Check that the literature and intro edits preserve formal content."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = "0aa0d8e70b684c9aa1d7a3533bc9937ecafe252f"
INTRO = "kagey-problems/problem131/paperD/sec_intro.tex"


def old(path):
    return subprocess.check_output(
        ["git", "show", f"{BASE}:{path}"], cwd=ROOT
    ).decode("utf-8").replace("\r\n", "\n")


def section(text, start, stop):
    return text.split(start, 1)[1].split(stop, 1)[0]


before = old(INTRO)
after = (ROOT / INTRO).read_text(encoding="utf-8")
theorems = r"\\begin\{theorem\}.*?\\end\{theorem\}"
displays = r"\\\[.*?\\\]"
require = {
    "intro_theorems_identical": re.findall(theorems, before, re.S)
    == re.findall(theorems, after, re.S),
    "intro_displays_identical": re.findall(displays, before, re.S)
    == re.findall(displays, after, re.S),
    "epigraph_identical": section(before, r"\begin{quote}", r"\medskip")
    == section(after, r"\begin{quote}", r"\medskip"),
    "callback_retained": (
        "As in the riddle, the evidence is left at the door: a walk that ends in the\n"
        "middle usually shows a reversal among its first few steps."
    ) in after,
}
result = {
    "baseline_commit": BASE,
    "checks": require,
    "all_checks_passed": all(require.values()),
    "intro_words_before": len(before.split()),
    "intro_words_after": len(after.split()),
    "scope": "Intro prose and bibliography only; full builds are checked separately.",
}
destination = Path(__file__).with_name("literature-edit-checks.json")
destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
if not result["all_checks_passed"]:
    raise SystemExit("A preserved region changed; inspect before continuing.")
