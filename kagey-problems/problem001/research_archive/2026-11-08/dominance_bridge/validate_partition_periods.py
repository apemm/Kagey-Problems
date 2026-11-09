"""Check every short periodic sea against independent finite geometry."""
from itertools import product
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "counting_followup"))
from dominance_compatibility import compatibility, allowed
from run_partitions import balanced_parts, accepts
from sea_sparse_automaton import forbidden_patterns, build_residuals


def main():
    started = time.monotonic()
    out = {
        "scope": "Bi-infinite periodic sea words; finite boundary pruning is allowed.",
        "max_period": 4,
        "partitions": [],
    }
    for h in (5, 6):
        L = 2 * (1 + (h - 1)**2 // 4)
        # A length-n period followed by L symbols contains every possible
        # full-support collision (horizontal span at most L), in every phase.
        cache = []
        for n in range(1, 5):
            for period in product(range(1, h + 1), repeat=n):
                word = tuple(period[j % n] for j in range(n + L))
                cache.append((word, compatibility(h, word)))
        for part in balanced_parts(h):
            patterns, _ = forbidden_patterns(h, time.monotonic() + 30, part=part)
            transition, _ = build_residuals(patterns, h)
            block = set(part)
            accepted = 0
            for word, geometric in cache:
                sparse = accepts(transition, word)
                assert sparse == allowed(geometric, block), (h, part, word)
                accepted += sparse
            result = {"height": h, "block": part,
                      "periods_checked": len(cache), "accepted": accepted,
                      "status": "passed"}
            out["partitions"].append(result)
            print(json.dumps(result), flush=True)
    patterns, _ = forbidden_patterns(6, time.monotonic() + 30)
    transition, _ = build_residuals(patterns, 6)
    word = (1, 1, 6, 1, 4, 6, 4)
    assert allowed(compatibility(6, word), {1, 3, 5})
    assert not accepts(transition, word)
    assert all(not allowed(compatibility(6, (r,) + word), {1, 3, 5})
               for r in range(1, 7))
    out["finite_boundary_witness"] = {
        "height": 6, "word": word, "finite_geometry_valid": True,
        "sparse_accepts": False, "every_one_column_left_extension_invalid": True,
    }
    out["elapsed_seconds"] = time.monotonic() - started
    out["status"] = "passed"
    (HERE / "partition_periodic_validation.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "partitions"}),
          flush=True)


if __name__ == "__main__":
    main()
