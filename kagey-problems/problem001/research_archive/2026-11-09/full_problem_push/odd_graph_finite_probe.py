"""Exact positive odd graph generation and bounded clique exploration."""
from __future__ import annotations
import argparse
import heapq
import json
from math import isqrt
from pathlib import Path
import time


def graph(limit):
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    vertices = list(range(1, limit + 1, 2))
    adj = {v: set() for v in vertices}
    for u in vertices:
        n, divisors = u, [1]
        while n > 1:
            p, exponent = spf[n], 0
            while n % p == 0:
                n //= p
                exponent += 1
            old = divisors[:]
            power = 1
            for _ in range(2 * exponent):
                power *= p
                divisors.extend(d * power for d in old)
        for a in divisors:
            b = u * u // a
            if a >= b:
                continue
            assert (b - a) % 8 == 0
            d = (b - a) // 4
            for v in (u - d, u + d):
                if 0 < v <= limit:
                    adj[u].add(v)
                    adj[v].add(u)
    return adj


def explore(limit, seconds):
    started = time.monotonic()
    adj = graph(limit)
    generated = time.monotonic()
    degree = {v: len(a) for v, a in adj.items()}
    heap = [(d, v) for v, d in degree.items()]
    heapq.heapify(heap)
    order, forward, degeneracy = [], {}, 0
    alive = set(adj)
    while heap:
        d, v = heapq.heappop(heap)
        if v not in alive or degree[v] != d:
            continue
        alive.remove(v)
        later = adj[v] & alive
        forward[v] = later
        order.append(v)
        degeneracy = max(degeneracy, len(later))
        for u in later:
            degree[u] -= 1
            heapq.heappush(heap, (degree[u], u))
    colors = {}
    for v in reversed(order):
        used = {colors[u] for u in adj[v] if u in colors}
        c = 0
        while c in used:
            c += 1
        colors[v] = c
    assert all(colors[v] != colors[u] for v in adj for u in adj[v])
    best, nodes, complete = [], 0, True
    deadline = generated + seconds

    def search(clique, candidates):
        nonlocal best, nodes
        nodes += 1
        if len(clique) + len(candidates) <= len(best):
            return
        if nodes % 4096 == 0 and time.monotonic() > deadline:
            raise TimeoutError
        while candidates:
            if len(clique) + len(candidates) <= len(best):
                return
            v = min(candidates, key=lambda w: len(adj[w] & candidates))
            candidates.remove(v)
            new = clique + [v]
            if len(new) > len(best):
                best = new
            search(new, candidates & adj[v])

    try:
        for v in reversed(order):
            search([v], forward[v].copy())
    except TimeoutError:
        complete = False
    witnesses = []
    for i, u in enumerate(best):
        for v in best[i + 1:]:
            found = False
            for a, b in ((u, v), (v, u)):
                n = a * a + 4 * (b - a) ** 2
                z = isqrt(n)
                if z * z == n:
                    witnesses.append([a, b, z])
                    found = True
                    break
            assert found
    return {
        "limit": limit,
        "vertices": len(adj),
        "edges": sum(map(len, adj.values())) // 2,
        "degeneracy": degeneracy,
        "greedy_colors": max(colors.values()) + 1,
        "clique": sorted(best),
        "clique_orientations_and_roots": witnesses,
        "clique_search_complete": complete,
        "search_nodes": nodes,
        "generation_seconds": generated - started,
        "total_seconds": time.monotonic() - started,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=100001)
    parser.add_argument("--seconds", type=float, default=120)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = explore(args.limit, args.seconds)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
