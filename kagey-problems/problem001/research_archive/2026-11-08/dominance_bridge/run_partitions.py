"""Bounded exact sea-shift graph comparison over balanced row partitions.

The sparse positive-pattern presentation is exact on bi-infinite words.
It can reject a valid finite board whose collision witness crosses an end.
The finite checks below therefore assert only the sound implication.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from fractions import Fraction
import gc
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path
import random
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "counting_followup"))
from dominance_compatibility import compatibility, allowed
from sea_sparse_automaton import (
    forbidden_patterns, build_residuals, build_graph, scc,
    exact_spectral_bounds, resident_bytes,
)


def balanced_parts(h):
    parts = list(combinations(range(1, h + 1), h // 2))
    return [p for p in parts if h % 2 or 1 in p]


def accepts(transition, word):
    state = 0
    for letter in word:
        state = transition(state, letter)
        if state is None:
            return False
    return True


def component_period(trans, h, comp, cid):
    start = next(v for v, c in enumerate(comp) if c == cid)
    distances = {start: 0}
    queue = deque([start])
    while queue:
        v = queue.popleft()
        for k in range(h):
            w = trans[v * h + k]
            if w >= 0 and comp[w] == cid and w not in distances:
                distances[w] = distances[v] + 1
                queue.append(w)
    period = 0
    for v, d in distances.items():
        for k in range(h):
            w = trans[v * h + k]
            if w >= 0 and comp[w] == cid:
                period = gcd(period, d + 1 - distances[w])
    assert period > 0
    return period


def run_part(h, part, deadline, args, exhaustive_cache):
    started = time.monotonic()
    result = {"block": list(part), "complete": False}
    patterns, stats = forbidden_patterns(h, deadline, part=part)
    result.update(stats)
    transition, nres = build_residuals(patterns, h)
    result["residual_universe"] = nres
    if resident_bytes() > args.memory_mb * 2**20:
        result["stop_reason"] = "memory cap after residual setup"
        return result
    states, trans, complete, bfs = build_graph(
        transition, h, deadline, args.states, args.memory_mb)
    result.update(bfs)
    result["states"] = len(states)
    result["complete"] = complete
    if not complete:
        result["elapsed_seconds"] = time.monotonic() - started
        return result

    result["edges"] = sum(w >= 0 for w in trans)
    comp, sizes, cyclic = scc(trans, h)
    result["scc_size_histogram"] = dict(Counter(sizes))
    constants = {}
    L = 2 * (1 + (h - 1)**2 // 4)
    for r in range(1, h + 1):
        v = 0
        for _ in range(L + 1):
            v = trans[v * h + r - 1]
            if v < 0:
                break
        if v >= 0:
            assert trans[v * h + r - 1] == v
            constants[r] = v
    assert 1 in constants and h in constants
    boundary = comp[constants[1]]
    assert comp[constants[h]] == boundary
    result["constant_states"] = constants
    result["boundary_component"] = boundary
    result["cyclic_components"] = []
    for cid in sorted(cyclic, key=lambda c: -sizes[c]):
        entry = {
            "id": cid, "size": sizes[cid],
            "period": component_period(trans, h, comp, cid),
            "constant_rows": [r for r, v in constants.items() if comp[v] == cid],
            "boundary_component": cid == boundary,
            "rho_bounds": exact_spectral_bounds(trans, h, comp, cid),
        }
        result["cyclic_components"].append(entry)
    result["unique_recurrent_boundary_component"] = len(cyclic) == 1 and boundary in cyclic
    result["overall_lower_fraction"] = str(max(
        Fraction(c["rho_bounds"]["lower_fraction"])
        for c in result["cyclic_components"]))
    result["overall_upper_fraction"] = str(max(
        Fraction(c["rho_bounds"]["upper_fraction"])
        for c in result["cyclic_components"]))

    checked = 0
    finite_boundary_pruned = 0
    block = set(part)
    for word, edges in exhaustive_cache:
        sparse = accepts(transition, word)
        geometric = allowed(edges, block)
        assert not sparse or geometric, (h, part, word)
        finite_boundary_pruned += geometric and not sparse
        checked += 1
    rng = random.Random(20261108 + h + sum(part))
    random_checks = 0
    for _ in range(args.random_checks):
        word, state = [], 0
        for _ in range(2 * L + 5):
            choices = [(r, transition(state, r)) for r in range(1, h + 1)]
            choices = [(r, s) for r, s in choices if s is not None]
            if not choices:
                break
            r, state = rng.choice(choices)
            word.append(r)
        sparse = accepts(transition, word)
        geometric = allowed(compatibility(h, word), block)
        assert not sparse or geometric, (h, part, word)
        finite_boundary_pruned += geometric and not sparse
        random_checks += 1
        if word:
            word[rng.randrange(len(word))] = rng.randrange(1, h + 1)
            sparse = accepts(transition, word)
            geometric = allowed(compatibility(h, word), block)
            assert not sparse or geometric, (h, part, word)
            finite_boundary_pruned += geometric and not sparse
            random_checks += 1
    result["validation"] = {
        "exhaustive_words": checked,
        "exhaustive_word_length": args.word_length,
        "long_walk_and_mutation_checks": random_checks,
        "finite_boundary_pruned": finite_boundary_pruned,
        "scope": "Sparse finite-word acceptance implies finite geometric validity.",
        "status": "passed",
    }
    result["elapsed_seconds"] = time.monotonic() - started
    return result


def main():
    p = argparse.ArgumentParser()
    p.add_argument("height", type=int)
    p.add_argument("--total-seconds", type=float, default=120)
    p.add_argument("--per-part-seconds", type=float, default=25)
    p.add_argument("--states", type=int, default=150000)
    p.add_argument("--memory-mb", type=int, default=512)
    p.add_argument("--word-length", type=int, default=5)
    p.add_argument("--random-checks", type=int, default=20)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    started = time.monotonic()
    deadline = started + args.total_seconds
    h = args.height
    cache = [(w, compatibility(h, w))
             for w in product(range(1, h + 1), repeat=args.word_length)]
    result = {
        "height": h, "expected_partitions": len(balanced_parts(h)),
        "total_seconds_cap": args.total_seconds, "memory_cap_mb": args.memory_mb,
        "partitions": [], "complete": False,
    }
    for part in balanced_parts(h):
        if time.monotonic() >= deadline:
            result["stop_reason"] = "collective time cap"
            break
        print(json.dumps({"phase": "partition", "height": h, "block": part}), flush=True)
        try:
            data = run_part(h, part, min(deadline, time.monotonic() + args.per_part_seconds),
                            args, cache)
        except TimeoutError as exc:
            data = {"block": list(part), "complete": False, "stop_reason": str(exc)}
        result["partitions"].append(data)
        result["elapsed_seconds"] = time.monotonic() - started
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({k: data[k] for k in
                          ("block", "complete", "states", "elapsed_seconds")
                          if k in data}), flush=True)
        gc.collect()
    result["complete"] = (len(result["partitions"]) == result["expected_partitions"]
                          and all(x["complete"] for x in result["partitions"]))
    if result["complete"]:
        odd = set(range(1, h + 1, 2))
        parity = next(x for x in result["partitions"]
                      if set(x["block"]) in (odd, set(range(1, h + 1)) - odd))
        others = [x for x in result["partitions"] if x is not parity]
        lower = Fraction(parity["overall_lower_fraction"])
        upper = max(Fraction(x["overall_upper_fraction"]) for x in others)
        result["parity_block"] = parity["block"]
        result["parity_lower_fraction"] = str(lower)
        result["other_max_upper_fraction"] = str(upper)
        result["parity_strictly_dominates"] = lower > upper
        result["parity_unique_recurrent_boundary_component"] = (
            parity["unique_recurrent_boundary_component"])
    result["elapsed_seconds"] = time.monotonic() - started
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "partitions"}), flush=True)


if __name__ == "__main__":
    main()
