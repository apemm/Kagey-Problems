"""Export exact residual transitions for the independent C# graph builder."""
from __future__ import annotations
import argparse
import importlib.util
from itertools import combinations
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "2026-11-08" / "dominance_bridge" / "sea_sparse_automaton.py"
spec = importlib.util.spec_from_file_location("sea_original", SOURCE)
sea = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sea)


def export(h, output, part=None, max_span=None, alphabet=None):
    patterns, stats = sea.forbidden_patterns(h, time.monotonic() + 300, part=part)
    physical_height = h
    physical_partition = sorted(part) if part is not None else list(range(1,h+1,2))
    if alphabet is not None:
        alphabet = sorted(set(alphabet))
        assert alphabet and min(alphabet) >= 1 and max(alphabet) <= h
        mapping = {r:i+1 for i,r in enumerate(alphabet)}
        patterns = [tuple((x,mapping[r]) for x,r in p) for p in patterns
                    if all(r in mapping for x,r in p)]
        h = len(alphabet)
        stats = dict(stats, restricted_alphabet=alphabet,
                     retained_patterns=len(patterns))
    if max_span is not None:
        patterns = [p for p in patterns if p[-1][0] <= max_span]
        stats = dict(stats, truncation_span=max_span,
                     retained_patterns=len(patterns))
    universe = set()
    for p in patterns:
        for age in range(1, p[-1][0]+1):
            universe.add(tuple((x-age, r) for x, r in p if x >= age))
    residuals = sorted(universe, key=lambda p: (
        len(p), tuple((x-p[0][0], r) for x, r in p), p[0][0]))
    index = {p: i for i, p in enumerate(residuals)}
    supersets = [[] for _ in residuals]
    subsets = [[] for _ in residuals]
    for i, p in enumerate(residuals):
        for size in range(1, len(p)+1):
            for sub in combinations(p, size):
                j = index.get(sub)
                if j is not None:
                    supersets[j].append(i)
                    subsets[i].append(j)
    successor = [-1] * len(residuals)
    match = [[] for _ in range(h+1)]
    reject = [[] for _ in range(h+1)]
    starts = [[] for _ in range(h+1)]
    wildcard = []
    for i, p in enumerate(residuals):
        if p[0][0] == 0 and len(p) == 1:
            reject[p[0][1]].append(i)
            continue
        tail = tuple((x-1, r) for x, r in p if x > 0)
        successor[i] = index[tail]
        if p[0][0] > 0:
            assert successor[i] == i-1
            wildcard.append(i)
        else:
            match[p[0][1]].append(i)
    for p in patterns:
        starts[p[0][1]].append(index[tuple((x-1, r) for x, r in p[1:])])
    for r in range(h+1):
        keep = []
        blocked = set()
        for i in sorted(set(starts[r])):
            if i not in blocked:
                keep.append(i)
                blocked.update(supersets[i])
        starts[r] = keep
    data = dict(height=h, count=len(residuals), successor=successor,
                supersets=supersets, subsets=subsets, wildcard=wildcard,
                match=match, reject=reject, starts=starts, geometry=stats,
                partition=physical_partition)
    if alphabet is not None:
        data.update(physical_height=physical_height, alphabet=alphabet)
    output.write_text(json.dumps(data, separators=(",", ":")), encoding="utf-8")
    print(json.dumps(dict(height=h, residuals=len(residuals), geometry=stats)))


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("height", type=int)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--part", help="Comma-separated rows in one partition class")
    p.add_argument("--max-span", type=int, help="Drop longer patterns, giving a certified entropy upper model")
    p.add_argument("--alphabet", help="Restrict physical rows, then encode them by consecutive symbol indices")
    a = p.parse_args()
    part = None if a.part is None else set(map(int, a.part.split(",")))
    alphabet = None if a.alphabet is None else list(map(int,a.alphabet.split(',')))
    export(a.height, a.output, part, a.max_span, alphabet)
