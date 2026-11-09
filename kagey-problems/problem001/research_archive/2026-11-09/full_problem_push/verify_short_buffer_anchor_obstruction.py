"""Verify the exact coordinates of the quadratic fixed-anchor family."""
import json
from pathlib import Path

def q(t):
    return (t * (t - 1) // 2) % 2

def add(a, b):
    return (a[0] + b[0], a[1] + b[1])

def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])

def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]

def diagonal_rectangle(a, c, b, d):
    assert add(a, c) == add(b, d)
    ac, bd = sub(c, a), sub(d, b)
    assert dot(ac, ac) == dot(bd, bd)
    assert ac[0] * bd[1] != ac[1] * bd[0]
    assert len({a, b, c, d}) == 4

records = []
for u in (1, 5, 9, 13, 101, 1001):
    h = 15 * u * u + 2
    a, c = (0, 1), (2 * u, 2)
    b = (18 * u**3 + 3 * u, 3 * u * u + 1)
    d = (18 * u**3 - u, h)
    t = (-u, 6 * u * u + 1)
    w, z = add(a, t), add(b, t)
    assert dot(sub(b, a), t) == 0
    diagonal_rectangle(a, z, b, w)
    diagonal_rectangle(c, d, w, z)
    assert all(1 <= p[1] <= h for p in (a, b, c, d, w, z))
    assert all(q(p[0]) == q(p[1]) for p in (a, b, c, d))
    assert all(q(p[0]) != q(p[1]) for p in (w, z))
    assert c[0] < d[0] < z[0] < b[0]
    records.append({
        "u": u, "height": h, "anchor": [a, c], "core": [b, d],
        "whites": [w, z], "first_core_distance": d[0] - c[0],
        "distance_over_height": (d[0] - c[0]) / h,
    })
out = {
    "passed": True,
    "scope": "Exact collision coordinates and protected phases; completion uses the proved two-point local lemma.",
    "records": records,
}
ordinary = []
for n in (1, 2, 5, 10, 100, 1000):
    s, p = 2 * n - 1, 2 * n * n
    y = p * s * s + 2
    x, v = p * y, y + 2 * p * s
    h = v + 1
    a, c = (0, 1), (1, 1)
    b, d = (x, y + 1), (x - 2 * s - 1, h)
    t = (-s, p * s)
    w, z = add(a, t), add(b, t)
    diagonal_rectangle(a, z, b, w)
    diagonal_rectangle(c, d, w, z)
    assert all(1 <= point[1] <= h for point in (a, b, c, d, w, z))
    assert all(point[1] % 2 == 1 for point in (a, b, c, d))
    assert c[0] < d[0] < z[0] < b[0]
    ordinary.append({
        "n": n, "height": h, "anchor": [a, c], "core": [b, d],
        "common_corners": [w, z], "first_core_distance": d[0] - 1,
        "distance_over_height": (d[0] - 1) / h,
    })
out["ordinary_records"] = ordinary
path = Path(__file__).with_name("short_buffer_anchor_obstruction_check.json")
path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"passed": True, "quadratic_cases": len(records),
                  "ordinary_cases": len(ordinary), "output": str(path)}))
