"""Exact Boolean phase SFT for full row-class Cartesian alphabets.

Only singleton-axis rivals and vertical-pair axis rivals are imposed.
This is not the full sea shift. Finite boundary words are normalized by
their constrained-column supports; recurrent existence is exact.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from itertools import combinations
import importlib.util
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
ENGINE = HERE.parents[1] / "2026-11-08" / "dominance_bridge" / "sea_sparse_automaton.py"
spec = importlib.util.spec_from_file_location("sea_engine", ENGINE)
engine = importlib.util.module_from_spec(spec)
assert spec.loader
spec.loader.exec_module(engine)


def representative(h, part):
    part = frozenset(part)
    complement = frozenset(set(range(1, h + 1)) - part)
    reflected = frozenset(h + 1 - r for r in part)
    candidates = [part, complement, reflected,
                  frozenset(set(range(1, h + 1)) - reflected)]
    return min((tuple(sorted(p)) for p in candidates), key=lambda p: (len(p), p))


def expected_parts(h):
    colorings = [
        [r % 2 for r in range(1, h + 1)],
        [(r * (r - 1) // 2) % 2 for r in range(1, h + 1)],
        [(r * (r - 1) // 2 + r) % 2 for r in range(1, h + 1)],
    ]
    return {representative(h, [r for r, c in enumerate(cs, 1) if c])
            for cs in colorings if abs(2 * sum(cs) - h) <= 1}


def forbidden_phase_patterns(h, part, shapes):
    part = set(part)
    color = lambda r: 1 + int(r in part)
    patterns = set()
    def insert(cells):
        p = engine.normalize(cells)
        if p is not None:
            patterns.add(p)
    for sh in shapes:
        for completion in sh:
            x, r = completion
            others = [p for p in sh if p != completion]
            # Three required black cells must occupy different columns,
            # even if their row colors happen to agree.
            if len({u for u, _ in others}) != 3:
                continue
            insert([(u, color(s)) for u, s in others] + [(x, 3 - color(r))])
        for white_pair in combinations(sh, 2):
            (x, r), (z, s) = white_pair
            if x != z or color(r) == color(s):
                continue
            others = [p for p in sh if p not in white_pair]
            if len({u for u, _ in others}) != 2:
                continue
            insert([(u, color(v)) for u, v in others])
    minimal, kept = [], set()
    for p in sorted(patterns, key=lambda p: (len(p), p)):
        if any(engine.normalize(sub) in kept
               for k in range(1, len(p))
               for sub in combinations(p, k)):
            continue
        minimal.append(p)
        kept.add(p)
    return minimal


def cycle_word(trans, comp, sizes, cyclic, alphabet=2):
    if not cyclic:
        return None
    cid = next(iter(cyclic))
    start = next(i for i, c in enumerate(comp) if c == cid)
    for letter in range(alphabet):
        target = trans[start * alphabet + letter]
        if target < 0 or comp[target] != cid:
            continue
        if target == start:
            return [letter]
        queue = deque([target])
        previous = {target: None}
        while queue:
            node = queue.popleft()
            if node == start:
                path = []
                while previous[node] is not None:
                    parent, lab = previous[node]
                    path.append(lab)
                    node = parent
                return [letter] + list(reversed(path))
            for lab in range(alphabet):
                nxt = trans[node * alphabet + lab]
                if nxt >= 0 and comp[nxt] == cid and nxt not in previous:
                    previous[nxt] = (node, lab)
                    queue.append(nxt)
    raise AssertionError("cyclic SCC had no cycle")


def check_periodic(patterns, word):
    period = len(word)
    return not any(all(word[(shift + x) % period] + 1 == a for x, a in p)
                   for p in patterns for shift in range(period))


def run(args):
    output = HERE / args.output
    result = {"scope": "singleton and vertical-rival full-row-class phase SFT",
              "maximum_retained_support_span": args.span,
              "heights": [], "started": time.time()}
    for h in args.heights:
        shapes = engine.tilted_shapes(h)
        parts = sorted({representative(h, p)
                        for p in combinations(range(1, h + 1), h // 2)})
        expected = expected_parts(h)
        row = {"height": h, "tilted_shapes": len(shapes),
               "partition_orbits": len(parts), "expected_orbits": sorted(expected),
               "partitions": []}
        result["heights"].append(row)
        for part in parts:
            started = time.monotonic()
            patterns = forbidden_phase_patterns(h, part, shapes)
            if args.span is not None:
                patterns = [p for p in patterns if p[-1][0] <= args.span]
            transition, nres = engine.build_residuals(patterns, 2)
            states, trans, complete, stats = engine.build_graph(
                transition, 2, started + args.seconds,
                args.state_cap, args.memory_mb)
            record = {"part": part, "patterns": len(patterns),
                      "pattern_sizes": dict(Counter(map(len, patterns))),
                      "residuals": nres, "states": len(states),
                      "complete": complete, **stats}
            if complete:
                comp, sizes, cyclic = engine.scc(trans, 2)
                word = cycle_word(trans, comp, sizes, cyclic)
                record.update({"has_biinfinite_phase": bool(cyclic),
                               "cyclic_components": len(cyclic),
                               "phase_witness": word,
                               "expected_protected_partition": part in expected})
                if word is not None:
                    assert check_periodic(patterns, word)
            record["seconds"] = round(time.monotonic() - started, 4)
            row["partitions"].append(record)
            output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
            print(json.dumps({"height": h, **record}), flush=True)
        row["complete"] = all(p["complete"] for p in row["partitions"])
        row["feasible_parts"] = [p["part"] for p in row["partitions"]
                                 if p.get("has_biinfinite_phase")]
        row["unexpected_feasible"] = [p["part"] for p in row["partitions"]
                                     if p.get("has_biinfinite_phase")
                                     and not p["expected_protected_partition"]]
        output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    result["seconds"] = time.time() - result["started"]
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--heights", nargs="+", type=int, default=[8, 9, 10])
    parser.add_argument("--seconds", type=float, default=5)
    parser.add_argument("--state-cap", type=int, default=30000)
    parser.add_argument("--memory-mb", type=float, default=256)
    parser.add_argument("--output", default="row_class_phase_sft_results.json")
    parser.add_argument("--span", type=int, default=None)
    run(parser.parse_args())
