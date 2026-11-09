"""Independent exact one-label geometry for the punctured (1,2,1) sea."""
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
import json
import time

HERE = Path(__file__).resolve().parent


def pair_rectangles(h, width, pairs):
    result = set()
    def add(corners):
        if len(set(corners)) != 4:
            return
        if len({x for x, y in corners}) == 2 and len({y for x, y in corners}) == 2:
            return
        result.add(tuple(sorted(y * width + x for x, y in corners)))
    for A, C in pairs:
        ax, ay = A
        cx, cy = C
        dx, dy = cx - ax, cy - ay
        sx, sy = ax + cx, ay + cy
        norm = dx * dx + dy * dy
        for by in range(h):
            rem = norm - (2 * by - sy) ** 2
            if rem < 0:
                continue
            root = isqrt(rem)
            if root * root != rem:
                continue
            for delta in {root, -root}:
                if (sx + delta) % 2:
                    continue
                bx, ex, ey = (sx + delta) // 2, (sx - delta) // 2, sy - by
                if 0 <= bx < width and 0 <= ex < width and 0 <= ey < h:
                    add((A, C, (bx, by), (ex, ey)))
        if not dx or not dy:
            continue
        divisor = gcd(abs(dx), abs(dy))
        vx, vy = -dy // divisor, dx // divisor
        lower, upper = -max(h, width), max(h, width)
        for base, step, bound in ((ax, vx, width - 1), (cx, vx, width - 1),
                                  (ay, vy, h - 1), (cy, vy, h - 1)):
            if step > 0:
                lower = max(lower, -(base // step))
                upper = min(upper, (bound - base) // step)
            else:
                lower = max(lower, -((base - bound) // step))
                upper = min(upper, (-base) // step)
        for k in range(lower, upper + 1):
            if k:
                add((A, C, (ax + k * vx, ay + k * vy),
                     (cx + k * vx, cy + k * vy)))
    return result


def check_height(h):
    span = 1 + (h - 1) ** 2 // 4
    center = 4 * ((2 * span + 3) // 4)
    width = 2 * center + 1
    cols = [set() if x % 4 == 0 else {0 if x % 2 else 1}
            for x in range(width)]
    sea = [(x, next(iter(rows))) for x, rows in enumerate(cols) if rows]
    black_sea = {r * width + x for x, r in sea}
    # A tilted rectangle with two sea points must use one point on each
    # low row as a side. Its horizontal side difference is at most h-2.
    # The diagonal alternative has row sum3 and only the same two rows,
    # making it axis-aligned. Same-row2 diagonals would require a multiple
    # of four to have squared length exactly four above another square.
    low = [(x, r) for x, r in sea if r == 0]
    high = [(x, r) for x, r in sea if r == 1]
    base = pair_rectangles(h, width,
        ((A, B) for A in low for B in high if abs(A[0] - B[0]) <= h))
    additions = [pair_rectangles(h, width,
        (((center, r), point) for point in sea)) for r in range(h)]
    tested, rect_count = 0, 0
    failures = []
    for edge in [()] + [E for E in combinations(range(h), 2) if (E[0] - E[1]) % 2]:
        black = black_sea | {r * width + center for r in edge}
        rectangles = set(base)
        for r in edge:
            rectangles.update(additions[r])
        if edge:
            rectangles.update(pair_rectangles(h, width,
                [((center, edge[0]), (center, edge[1]))]))
        cols[center] = set(edge)
        presentations = {}
        def fail(kind, rectangle, white):
            return {'height': h, 'width': width, 'center': center,
                    'edge': [r + 1 for r in edge], 'kind': kind,
                    'rectangle': [(p % width - center, p // width + 1) for p in rectangle],
                    'white': [(p % width - center, p // width + 1) for p in white],
                    'previous': [(p % width - center, p // width + 1)
                                 for p in presentations.get(white, ())]}
        failure = None
        for rectangle in rectangles:
            white = tuple(p for p in rectangle if p not in black)
            if not white or white in presentations:
                failure = fail('hidden_or_duplicate', rectangle, white)
                break
            presentations[white] = rectangle
            if len(white) == 1:
                x, r = white[0] % width, white[0] // width
                if x % 4 == 0 or any((r - s) % 2 for s in cols[x]):
                    failure = fail('singleton_axis_rival', rectangle, white)
                    break
            else:
                assert len(white) == 2
                x, r = white[0] % width, white[0] // width
                z, s = white[1] % width, white[1] // width
                if x == z and (r - s) % 2:
                    failure = fail('vertical_axis_rival', rectangle, white)
                    break
                if r == s and cols[x] & cols[z]:
                    failure = fail('horizontal_axis_rival', rectangle, white)
                    break
                if x != z and r != s and s in cols[x] and r in cols[z]:
                    failure = fail('oblique_axis_rival', rectangle, white)
                    break
        if failure:
            failures.append(failure)
        tested += 1
        rect_count += len(rectangles)
    expected = {(1, 4 * v * v + 2) for v in range(1, isqrt(h) + 1, 2)
                if 4 * v * v + 2 <= h}
    actual = {tuple(f['edge']) for f in failures}
    return {'height': h, 'status': 'PASS' if actual == expected else 'DISCREPANCY',
            'cases': tested, 'weak_rectangles_checked': rect_count,
            'expected_bad_edges': sorted(expected), 'failures': failures}


def main():
    begin = time.monotonic()
    results = []
    for h in range(4, 31):
        result = check_height(h)
        results.append(result)
        print(json.dumps(result), flush=True)
        (HERE / 'low_two_sea_one_label_check.json').write_text(
            json.dumps({'results': results, 'seconds': time.monotonic() - begin}, indent=2) + '\n')
        if result.get('status') != 'PASS':
            break


if __name__ == '__main__':
    main()
