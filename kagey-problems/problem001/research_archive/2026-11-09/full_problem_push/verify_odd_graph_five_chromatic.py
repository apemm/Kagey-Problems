"""Independent arithmetic and DSATUR check of the five-chromatic witness."""
import json
from pathlib import Path
import time

p = Path(__file__).with_name("odd_graph_five_chromatic.json")
data = json.loads(p.read_text(encoding="utf-8"))
vs = data["vertices"]
index = {v: i for i, v in enumerate(vs)}
neighbors = [set() for _ in vs]
for u, v, base, root in data["edges_with_base_and_root"]:
    assert u in index and v in index and u != v and base in (u, v)
    assert root * root == base * base + 4 * (v - u) ** 2
    neighbors[index[u]].add(index[v])
    neighbors[index[v]].add(index[u])
upper = {int(v): c for v, c in data["upper_coloring"].items()}
assert set(upper) == set(vs)
assert all(0 <= c < 5 for c in upper.values())
assert all(upper[vs[v]] != upper[vs[u]] for v in range(len(vs)) for u in neighbors[v])

colors = [-1] * len(vs)
counts = [[0] * 4 for _ in vs]
uncolored = set(range(len(vs)))
nodes = 0
started = time.monotonic()


def solve(max_used):
    global nodes
    nodes += 1
    if not uncolored:
        return True
    v = max(uncolored, key=lambda i: (sum(bool(n) for n in counts[i]), len(neighbors[i])))
    forbidden = counts[v]
    if all(forbidden):
        return False
    uncolored.remove(v)
    for c in range(min(4, max_used + 2)):
        if forbidden[c]:
            continue
        colors[v] = c
        for u in neighbors[v]:
            counts[u][c] += 1
        if solve(max(max_used, c)):
            return True
        for u in neighbors[v]:
            counts[u][c] -= 1
        colors[v] = -1
    uncolored.add(v)
    return False


assert not solve(-1)
result = {
    "vertices": len(vs),
    "edges": sum(map(len, neighbors)) // 2,
    "largest_odd_vertex": max(vs),
    "all_arithmetic_edges_verified": True,
    "five_coloring_verified": True,
    "four_coloring_exists": False,
    "independent_search_nodes": nodes,
    "seconds": time.monotonic() - started,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
