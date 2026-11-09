"""Coordinate checks of the one-prime scaffold and its P coloring."""

from math import isqrt
import heapq
import json
import time

from quadratic_arithmetic_check import prime_after, right_angles, vertical_p


def tau(n):
    answer = 1
    factor = 2
    while factor * factor <= n:
        exponent = 0
        while n % factor == 0:
            n //= factor
            exponent += 1
        answer *= exponent + 1
        factor += 1
    return answer * (2 if n > 1 else 1)


def color_block(h, b):
    no = (h + 1) // 2
    adjacency = [set() for _ in range(no)]
    directed_counts = []
    for a in range(no):
        u = 2 * a - 2 * b - 1
        square = u * u
        targets = set()
        for r in range(1, abs(u)):
            if square % r:
                continue
            s = square // r
            if (s - r) % 8:
                continue
            delta = (s - r) // 8
            for c in (a - delta, a + delta):
                if 0 <= c < no:
                    targets.add(c)
                    adjacency[a].add(c)
                    adjacency[c].add(a)
        assert len(targets) <= tau(square) - 1
        directed_counts.append(len(targets))
    degree = [len(neighbors) for neighbors in adjacency]
    heap = [(d, a) for a, d in enumerate(degree)]
    heapq.heapify(heap)
    active = set(range(no))
    order = []
    degeneracy = 0
    while heap:
        d, a = heapq.heappop(heap)
        if a not in active or d != degree[a]:
            continue
        active.remove(a)
        order.append(a)
        degeneracy = max(degeneracy, d)
        for c in adjacency[a] & active:
            degree[c] -= 1
            heapq.heappush(heap, (degree[c], c))
    colors = {}
    for a in reversed(order):
        used = {colors[c] for c in adjacency[a] if c in colors}
        color = 0
        while color in used:
            color += 1
        colors[a] = color
    assert all(colors[a] != colors[c] for a in range(no) for c in adjacency[a])
    return colors, degeneracy, sum(map(len, adjacency)) // 2, max(directed_counts, default=0)


def run(h):
    p = prime_after(10 * h)
    no, ne = (h + 1) // 2, h // 2
    period = p * ne
    base, lifted = [], []
    colors_used, degeneracy, edges, largest_out = 1, 0, 0, 0
    dh = max(tau(u * u) - 1 for u in range(1, h, 2))
    for b in range(ne):
        colors, d, e, out = color_block(h, b)
        degeneracy = max(degeneracy, d)
        edges += e
        largest_out = max(largest_out, out)
        colors_used = max(colors_used, 1 + max(colors.values()))
        for a in range(no):
            slot = a + p * b
            base.extend(((4 * slot, 2 * a + 1), (4 * slot, 2 * b + 2)))
            lifted_slot = slot + 2 * colors[a] * period
            lifted.extend(((4 * lifted_slot, 2 * a + 1), (4 * lifted_slot, 2 * b + 2)))
    assert degeneracy <= 2 * dh
    assert colors_used <= 2 * dh + 1
    assert right_angles(base) is None, (h, "base")
    assert right_angles(lifted) is None, (h, "lifted")
    assert vertical_p(h, lifted) is None, (h, "P")
    return {"height": h, "prime": p, "double_edges": no * ne,
            "P_graph_edges": edges, "largest_directed_outdegree": largest_out,
            "degeneracy": degeneracy, "colors": colors_used,
            "proved_palette_bound": 2 * dh + 1,
            "base_width": max(x for x, _ in base) + 1,
            "lifted_width": max(x for x, _ in lifted) + 1}


if __name__ == "__main__":
    start = time.monotonic()
    results = [run(h) for h in range(3, 42)]
    print(json.dumps({"results": results, "seconds": time.monotonic() - start}, indent=2))
