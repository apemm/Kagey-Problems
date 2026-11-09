"""Small exact test of a proposed reflection-closure stability inequality."""
from itertools import combinations
from fractions import Fraction
from pathlib import Path
import json
import time

HERE = Path(__file__).resolve().parent
results = []
started = time.monotonic()
for h in range(6, 21):
    best = None
    example = None
    tested = 0
    even_mask = sum(1 << (r - 1) for r in range(2, h + 1, 2))
    center_masks = [((1 << (h - 2 * k)) - 1) << k
                    for k in range(1, (h - 1) // 2 + 1)]
    for size in sorted({h // 2, (h + 1) // 2}):
        for positions in combinations(range(h), size):
            mask = sum(1 << i for i in positions)
            ne = (mask & even_mask).bit_count()
            no = size - ne
            if not ne or not no:
                continue
            violations = sum(
                (((mask >> k) ^ (mask << k)) & mask & center_masks[k - 1]).bit_count()
                for k in range(1, len(center_masks) + 1))
            ratio = Fraction(violations, ne * no)
            tested += 1
            if best is None or ratio < best:
                best = ratio
                example = [i + 1 for i in positions]
    row = {"height": h, "tested": tested,
           "minimum_ratio_V_over_even_times_odd": str(best),
           "example": example}
    results.append(row)
    print(json.dumps(row), flush=True)
(HERE / "reflection_even_odd_probe.json").write_text(
    json.dumps({"scope": "finite exact probe, not a theorem",
                "results": results,
                "seconds": time.monotonic() - started}, indent=2) + "\n",
    encoding="utf-8")

