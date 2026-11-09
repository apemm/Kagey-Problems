"""Verify one exact oblique rival in the two-prime CRT placement."""
from itertools import combinations, product
import json
from math import isqrt
from pathlib import Path


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def main():
    h, p, q = 4469, 89209, 89563
    w, t, d, z = 22, 4063, 177, 89386
    K = (t-1)//2
    assert d == 8*w+1 and z == w*t
    assert p == z-d and q == z+d
    assert is_prime(p) and is_prime(q)
    assert 10*h < p < 20*h < q < 40*h
    assert h >= t+2*d+3
    edges = [(1, 1+K+d), (1+d, 1+K),
             (0, K+d), (d, K)]
    assert all(0 <= a < (h+1)//2 and 0 <= b < h//2 for a,b in edges)
    raw = [a+p*((b-a)*pow(p,-1,q) % q) for a,b in edges]
    columns = [4*x for x in raw]
    rows = [(2*a+1, 2*b+2) for a,b in edges]
    black = {x: set(rr) for x,rr in zip(columns, rows)}
    A = (columns[0], rows[0][0])
    B = (columns[1], rows[1][1])
    C = (columns[2], rows[2][1])
    D = (columns[3], rows[3][0])
    W, Z = (columns[2], D[1]), (columns[3], C[1])
    U = tuple(b-a for a,b in zip(A,B))
    V = tuple(d-c for c,d in zip(C,D))
    H = tuple(a+b-c-d for a,b,c,d in zip(A,B,C,D))
    assert U == (4*z,t) and V == (4*z,-t)
    assert sum(u*h for u,h in zip(U,H)) == 0
    assert sum(u*u for u in U) == sum(v*v for v in V)
    assert tuple(a+b for a,b in zip(W,Z)) == tuple(c+d for c,d in zip(C,D))
    for R in ({A,B,W,Z}, {C,D,W,Z}):
        assert sorted(P for P in R if P[1] not in black.get(P[0], set())) == sorted((W,Z))
    p_edges = []
    for i,j in combinations(range(4),2):
        dx = abs(columns[i]-columns[j])
        for r,s in product(rows[i], rows[j]):
            if (r-s) % 2 == 0:
                continue
            norm = dx*dx+(r-s)**2
            length = isqrt(norm)
            if length*length != norm:
                continue
            if (r+s-length) % 2 == 0:
                low,high = (r+s-length)//2,(r+s+length)//2
                if 1 <= low < high <= h:
                    p_edges.append((i,j,r,s,low,high))
    assert not p_edges
    out = {"height": h, "primes": [p,q], "parameters": {"w":w,"t":t,"d":d,"z":z},
           "edge_indices": edges, "columns": columns, "double_rows": rows,
           "black_points": [A,B,C,D], "white_pair": [W,Z],
           "side_vector": U, "other_diagonal": V, "twice_connector": H,
           "pythagorean_pairs_among_four_edges": p_edges, "status": "passed"}
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(out,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(out),flush=True)


if __name__ == "__main__":
    main()

