"""Cross-check the memoized middle-cell model count by component truth tables."""
from itertools import product
from math import prod
from pathlib import Path
import json

path = Path(__file__).with_name("middle_count_h11.json")
data = json.loads(path.read_text())
clauses = data["constraints"]
n = len(data["order"]) - 1
adj = {j: set() for j in range(1, n + 1)}
for clause in clauses:
    for v in clause:
        adj[abs(v)].update(abs(w) for w in clause if abs(w) != abs(v))
seen = set()
results = []
for j in adj:
    if j in seen:
        continue
    todo, component = [j], []
    seen.add(j)
    while todo:
        v = todo.pop()
        component.append(v)
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                todo.append(w)
    component.sort()
    relevant = [c for c in clauses if any(abs(v) in component for v in c)]
    count = 0
    for values in product((False, True), repeat=len(component)):
        assignment = dict(zip(component, values))
        if not any(all(assignment[abs(v)] == (v > 0) for v in c) for c in relevant):
            count += 1
    results.append({"variables_one_based": component, "assignments": count})
total = prod(item["assignments"] for item in results)
assert total == data["valid_middle_assignments"] == 384
output = {"method": "exhaustive component truth tables", "components": results, "total": total}
path.with_name("middle_count_h11_independent.json").write_text(json.dumps(output, indent=2) + "\n")
print(json.dumps(output, indent=2))
