"""Extract and record a small exactly non-k-colorable odd graph."""
from __future__ import annotations
import argparse
import json
from math import isqrt
from pathlib import Path
import random
import time
from odd_graph_finite_probe import graph
from odd_graph_color_probe import color_probe


def induced(adj, vertices):
    return {v: adj[v] & vertices for v in vertices}


def run(limit, k, seconds, output):
    started = time.monotonic()
    adj = graph(limit)
    first = color_probe(limit, k, min(60, seconds), adj)
    assert first["status"] == "not_colorable", first["status"]
    alive = set(first["core_list"])
    rng = random.Random(4102026)
    attempts, removed, unknown = 0, 0, 0
    for round_id in range(3):
        candidates = sorted(alive, reverse=True)
        if round_id:
            rng.shuffle(candidates)
        for v in candidates:
            if v not in alive or time.monotonic() - started > seconds:
                continue
            test_vertices = alive - {v}
            result = color_probe(limit, k, 10, induced(adj, test_vertices))
            attempts += 1
            if result["status"] == "not_colorable":
                removed += len(alive) - len(result["core_list"])
                alive = set(result["core_list"])
                print(json.dumps({"remaining": len(alive), "attempts": attempts}), flush=True)
            elif result["status"] == "unknown":
                unknown += 1
        if time.monotonic() - started > seconds:
            break
    final = color_probe(limit, k, 60, induced(adj, alive))
    assert final["status"] == "not_colorable"
    upper = color_probe(limit, k + 1, 60, induced(adj, alive))
    edges = []
    for u in sorted(alive):
        for v in sorted(adj[u] & alive):
            if u >= v:
                continue
            for a, b in ((u, v), (v, u)):
                z = isqrt(a * a + 4 * (b - a) ** 2)
                if z * z == a * a + 4 * (b - a) ** 2:
                    edges.append([u, v, a, z])
                    break
            else:
                raise AssertionError((u, v))
    data = {
        "vertices": sorted(alive), "edges_with_base_and_root": edges,
        "not_colorable_with": k, "search_nodes": final["nodes"],
        "upper_coloring": upper["coloring"],
        "attempts": attempts, "removed": removed, "unknown_tests": unknown,
        "seconds": time.monotonic() - started,
    }
    output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in data.items()
                      if key not in ("edges_with_base_and_root", "upper_coloring")}))


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--limit", type=int, default=3001)
    p.add_argument("--colors", type=int, default=4)
    p.add_argument("--seconds", type=float, default=600)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    run(a.limit, a.colors, a.seconds, a.output)
