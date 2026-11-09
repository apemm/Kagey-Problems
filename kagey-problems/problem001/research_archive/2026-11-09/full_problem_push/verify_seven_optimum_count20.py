"""Independent core catalog, reflection expansion, and presentations at 7 by 20.

Incomplete solver records give a verified lower bound, never an exact count.
Exhaustion itself relies on the completed SAT records.
"""
from collections import defaultdict
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json
import time

HERE = Path(__file__).resolve().parent
H, W, TARGET = 7, 20, 31


def reflect_mask(mask):
    return sum(1 << (6-r) for r in range(H) if mask >> r & 1)


def canon(core):
    core = tuple(sorted(core))
    return min(core, tuple(sorted(map(reflect_mask, core))))


def columns(black):
    return [sum(1 << r for r in range(H) if black >> (r*W+c) & 1)
            for c in range(W)]


def reflect_board(black, horizontal, vertical):
    return sum(1 << ((6-r if vertical else r)*W +
                    (W-1-c if horizontal else c))
               for r in range(H) for c in range(W)
               if black >> (r*W+c) & 1)


def main():
    began = time.monotonic()
    pairs = list(combinations(range(H), 2))
    pair_indices = {pair: i for i, pair in enumerate(pairs)}
    pair_masks = [(1 << a) | (1 << b) for a, b in pairs]
    triangles = [sum(1 << pair_indices[p] for p in combinations(triple, 2))
                 for triple in combinations(range(H), 3)]
    families = {}
    for size in (11, 12):
        raw, quotient = set(), set()
        for edges in combinations(range(21), size):
            bits = sum(1 << i for i in edges)
            if any(bits & tri == tri for tri in triangles):
                continue
            core = tuple(sorted(pair_masks[i] for i in edges))
            raw.add(core)
            quotient.add(canon(core))
        assert len(raw) == (420 if size == 11 else 35)
        assert len(quotient) == (210 if size == 11 else 19)
        families[size] = quotient
    catalog = sorted([(0, core) for core in families[11]] +
                     [(1, core) for core in families[12]])
    assert len(catalog) == 229
    complete, attempted, hashes = {}, set(), {}
    for path in sorted(HERE.glob("excess_eleven_count_w20*.jsonl")):
        data = path.read_bytes()
        hashes[path.name] = sha256(data).hexdigest()
        lines = data.splitlines()
        for line_number, line in enumerate(lines):
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                # A running writer can leave only its final record incomplete.
                assert line_number == len(lines)-1 and not data.endswith(b"\n")
                continue
            index = record["index"]
            attempted.add(index)
            empty, core = catalog[index]
            assert record["width"] == W and record["target"] == TARGET
            assert record["core"]["empty_columns"] == empty
            assert tuple(record["core"]["masks"]) == core
            if record["status"] != "complete":
                continue
            if index in complete:
                old = complete[index]
                assert old["weighted_count"] == record["weighted_count"]
                assert set(old["models"]) == set(record["models"])
            complete[index] = record
    all_boards, projected, weighted = set(), [], 0
    positive = []
    for index, record in sorted(complete.items()):
        empty, core = catalog[index]
        vertical_weight = 1 if tuple(sorted(map(reflect_mask, core))) == core else 2
        assert record["vertical_weight"] == vertical_weight
        assert len(record["models"]) == len(set(record["models"]))
        subtotal = 0
        for encoded in record["models"]:
            black = int(encoded, 16)
            assert 0 <= black < (1 << (H*W))
            assert black.bit_count() == TARGET
            masks = columns(black)
            assert tuple(sorted(m for m in masks if m.bit_count() >= 2)) == core
            assert masks.count(0) == empty
            assert masks.index(core[0]) < W//2
            subtotal += 2*vertical_weight
            projected.append(dict(index=index, black=encoded,
                                  weight=2*vertical_weight))
            for horizontal, vertical in product((False, True), repeat=2):
                all_boards.add(reflect_board(black, horizontal, vertical))
        assert subtotal == record["weighted_count"]
        weighted += subtotal
        if subtotal:
            positive.append(dict(index=index, count=subtotal))
    assert weighted == len(all_boards)
    diagonal_groups = defaultdict(list)
    cells = [(c, r, r*W+c) for r in range(H) for c in range(W)]
    for (x, y, p), (u, v, q) in combinations(cells, 2):
        diagonal_groups[(x+u, y+v, (x-u)**2+(y-v)**2)].append((p, q))
    rectangles = set()
    for diagonals in diagonal_groups.values():
        for first, second in combinations(diagonals, 2):
            vertices = set(first+second)
            assert len(vertices) == 4
            rectangles.add(sum(1 << p for p in vertices))
    boards = []
    bounds = {9:17, 10:18, 11:20, 12:21, 13:23, 14:24,
              15:25, 16:26, 17:27, 18:29, 19:30}
    for black in sorted(all_boards):
        presentations = {rectangle & ~black for rectangle in rectangles}
        assert len(presentations) == len(rectangles)
        masks = columns(black)
        for length, bound in bounds.items():
            assert max(sum(m.bit_count() for m in masks[i:i+length])
                       for i in range(W-length+1)) <= bound
        boards.append(dict(black=hex(black),
                           column_word=",".join(
                               "".join(str(r+1) for r in range(H) if mask >> r & 1)
                               or "-" for mask in masks),
                           presentations=len(presentations)))
    for name in ("count_seven_excess_eleven.py", "fixed_row_core_sat.py",
                 "seven_row_equality_sat.py", "verify_seven_optimum_count20.py"):
        hashes[name] = sha256((HERE/name).read_bytes()).hexdigest()
    missing = sorted(set(range(229))-complete.keys())
    result = dict(status="PASS" if not missing else "PARTIAL",
                  height=H, width=W, optimum=TARGET,
                  optimum_count=weighted if not missing else None,
                  verified_count_lower_bound=weighted,
                  completed_cores=len(complete), attempted_cores=len(attempted),
                  missing_indices=missing,
                  unattempted_indices=sorted(set(range(229))-attempted),
                  positive_cores=positive, projected_model_count=len(projected),
                  projected_models=projected, rectangles=len(rectangles),
                  boards=boards, seconds=time.monotonic()-began,
                  source_sha256=hashes,
                  scope="Independent core generation, reflection expansion, and "
                        "actual rectangle presentations. Exhaustion relies on "
                        "completed SAT records; incomplete coverage is only a "
                        "verified lower bound.")
    (HERE/"seven_optimum_count20_independent_check.json").write_text(
        json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items()
                      if k not in ("boards", "projected_models", "source_sha256")},
                     indent=2))


if __name__ == "__main__":
    main()
