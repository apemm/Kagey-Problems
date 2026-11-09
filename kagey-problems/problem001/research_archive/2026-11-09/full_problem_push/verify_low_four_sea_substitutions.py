"""Test isolated parity doubles in the full periodic sea (4,1,2,1)."""
from itertools import combinations
from pathlib import Path
import json
import time
from verify_low_two_sea_one_label import pair_rectangles

HERE = Path(__file__).resolve().parent


def check(h):
    W = 1 + (h - 1) ** 2 // 4
    center = 4 * ((2 * W + 3) // 4)
    width = 2 * center + 5
    row = lambda x: (3, 0, 1, 0)[x % 4]
    cols = [{row(x)} for x in range(width)]
    sea = [(x, row(x)) for x in range(width) if x != center]
    seed = pair_rectangles(h, width,
        (((center + a, row(a)), (center + a + d, row(a + d)))
         for a in range(4) for d in range(1, W + 1)))
    shapes = set()
    for R in seed:
        points = [(p % width, p // width) for p in R]
        shift = 4 * (min(x for x, r in points) // 4)
        shapes.add(tuple(sorted((x - shift, r) for x, r in points)))
    base = set()
    for shape in shapes:
        maximum = max(x for x, r in shape)
        for shift in range(0, width - maximum, 4):
            base.add(tuple(sorted(r * width + x + shift for x, r in shape)))
    additions = [pair_rectangles(h, width,
        (((center, r), point) for point in sea)) for r in range(h)]
    black_sea = {r * width + x for x, r in sea}
    failures = []
    for edge in combinations(range(h), 2):
        if (edge[0] - edge[1]) % 2 == 0:
            continue
        black = black_sea | {r * width + center for r in edge}
        cols[center] = set(edge)
        rectangles = base | additions[edge[0]] | additions[edge[1]]
        rectangles |= pair_rectangles(h, width,
            [((center, edge[0]), (center, edge[1]))])
        seen = {}
        for R in rectangles:
            white = tuple(p for p in R if p not in black)
            if len(white) > 2:
                continue
            reason = None
            if not white or white in seen:
                reason = 'hidden_or_duplicate'
            elif len(white) == 1:
                x, r = white[0] % width, white[0] // width
                if any((r - s) % 2 for s in cols[x]):
                    reason = 'singleton_axis'
            else:
                x, r = white[0] % width, white[0] // width
                z, s = white[1] % width, white[1] // width
                if (x == z and (r - s) % 2 or r == s and cols[x] & cols[z]
                    or x != z and r != s and s in cols[x] and r in cols[z]):
                    reason = 'pair_axis'
            if reason:
                coordinate = lambda values: [(p % width - center, p // width + 1) for p in values]
                failures.append({'edge': [r + 1 for r in edge], 'reason': reason,
                                 'rectangle': coordinate(R), 'white': coordinate(white),
                                 'other': coordinate(seen.get(white, ()))})
                break
            seen[white] = R
    return {'height': h, 'tested_edges': h * h // 4,
            'failed_edges': len(failures), 'failures': failures}


def main():
    begin = time.monotonic()
    records = []
    for h in range(4, 21):
        records.append(check(h))
        print(json.dumps(records[-1]), flush=True)
        (HERE / 'low_four_sea_substitutions.json').write_text(json.dumps(
            {'results': records, 'seconds': time.monotonic() - begin}, indent=2) + '\n')


if __name__ == '__main__':
    main()
