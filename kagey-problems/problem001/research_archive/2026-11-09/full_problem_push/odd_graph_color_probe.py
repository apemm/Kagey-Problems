"""Bounded exact k-coloring search, with low-degree peeling and propagation."""
from __future__ import annotations
import argparse
from collections import deque
import json
from pathlib import Path
import time
from odd_graph_finite_probe import graph


def color_probe(limit, k, seconds, adj_input=None):
    started = time.monotonic()
    adj = graph(limit) if adj_input is None else adj_input
    alive = set(adj)
    degree = {v: len(a) for v, a in adj.items()}
    queue = deque(v for v in adj if degree[v] < k)
    peeled = []
    while queue:
        v = queue.popleft()
        if v not in alive:
            continue
        alive.remove(v)
        peeled.append(v)
        for u in adj[v] & alive:
            degree[u] -= 1
            if degree[u] == k - 1:
                queue.append(u)
    vertices = sorted(alive, key=lambda v: (-degree[v], v))
    index = {v: i for i, v in enumerate(vertices)}
    links = [[index[u] for u in adj[v] & alive] for v in vertices]
    full = (1 << k) - 1
    domains = [full] * len(vertices)
    trail, nodes = [], 0
    deadline = started + seconds
    solution = None

    def force(v, mask):
        pending = [(v, mask)]
        while pending:
            v, mask = pending.pop()
            if not (domains[v] & mask):
                return False
            if domains[v] == mask:
                continue
            trail.append((v, domains[v]))
            domains[v] = mask
            for u in links[v]:
                if domains[u] & mask:
                    new = domains[u] & ~mask
                    if not new:
                        return False
                    trail.append((u, domains[u]))
                    domains[u] = new
                    if new & (new - 1) == 0:
                        # Restore it until force processes and propagates it.
                        domains[u] = trail.pop()[1]
                        pending.append((u, new))
        return True

    def undo(mark):
        while len(trail) > mark:
            v, value = trail.pop()
            domains[v] = value

    def dfs():
        nonlocal nodes, solution
        nodes += 1
        if nodes % 128 == 0 and time.monotonic() > deadline:
            raise TimeoutError
        candidates = [i for i, d in enumerate(domains) if d & (d - 1)]
        if not candidates:
            solution = domains[:]
            return True
        v = min(candidates, key=lambda i: (domains[i].bit_count(), -len(links[i])))
        choices = domains[v]
        while choices:
            bit = choices & -choices
            choices ^= bit
            mark = len(trail)
            if force(v, bit) and dfs():
                return True
            undo(mark)
        return False

    status = "unknown"
    try:
        if vertices:
            assert force(0, 1)
        sat = dfs()
        status = "colorable" if sat else "not_colorable"
    except TimeoutError:
        pass
    coloring = None
    if solution is not None:
        coloring = {vertices[i]: d.bit_length() - 1 for i, d in enumerate(solution)}
        for v in reversed(peeled):
            used = {coloring[u] for u in adj[v] if u in coloring}
            coloring[v] = next(c for c in range(k) if c not in used)
        assert all(coloring[v] != coloring[u] for v in adj for u in adj[v])
    return {
        "limit": limit, "colors": k, "status": status,
        "core_vertices": len(vertices),
        "core_list": vertices,
        "core_edges": sum(map(len, links)) // 2,
        "nodes": nodes, "seconds": time.monotonic() - started,
        "coloring": coloring,
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--limit", type=int, required=True)
    p.add_argument("--colors", type=int, default=4)
    p.add_argument("--seconds", type=float, default=30)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    result = color_probe(a.limit, a.colors, a.seconds)
    a.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("coloring", "core_list")}, indent=2))
