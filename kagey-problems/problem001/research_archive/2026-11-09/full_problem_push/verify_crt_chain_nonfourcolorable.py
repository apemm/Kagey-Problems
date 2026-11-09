"""Independent exact CNF, RUP, and in-strip geometry verification.

Uses only the Python standard library and does not import a SAT solver or
the graph/proof generator.  Deletion lines are safely ignored: every
addition is checked against the original clauses and prior additions.
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from math import isqrt
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent
N = 150
T = 375
CLIQUE = (0, 23, 68, 133)


def square(n):
    z = isqrt(n)
    return z if z * z == n else None


def load_cnf(path, variables=4*N):
    clauses, pending, declared = [], [], None
    for line in path.read_text(encoding="ascii").splitlines():
        line = line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            fields = line.split()
            assert fields[:2] == ["p", "cnf"] and declared is None
            declared = tuple(map(int, fields[2:]))
            continue
        for lit in map(int, line.split()):
            if lit:
                pending.append(lit)
            else:
                clauses.append(tuple(pending))
                pending = []
    assert not pending and declared == (variables, len(clauses))
    assert all(1 <= abs(v) <= variables for c in clauses for v in c)
    return clauses


def rup(clauses, learned):
    """Negate the proposed clause, then repeatedly scan for units."""
    assigned = {}
    trace = []
    for lit in learned:
        variable, value = abs(lit), lit < 0
        assert variable not in assigned or assigned[variable] == value
        assigned[variable] = value
    while True:
        progress = False
        for number, clause in enumerate(clauses):
            remaining = []
            for lit in clause:
                value = assigned.get(abs(lit))
                if value is None:
                    remaining.append(lit)
                elif value == (lit > 0):
                    break
            else:
                if not remaining:
                    return {"learned": list(learned),
                            "propagations": len(trace),
                            "conflict_clause_index": number,
                            "conflict_clause": list(clause),
                            "unit_trace": trace}
                if len(remaining) == 1:
                    lit = remaining[0]
                    assert abs(lit) not in assigned
                    assigned[abs(lit)] = lit > 0
                    trace.append([number, lit])
                    progress = True
        if not progress:
            raise AssertionError(("Not RUP", learned))


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def next_prime(n):
    n += 1
    while not prime(n):
        n += 1
    return n


def main():
    cnf_path = HERE / "crt_chain_t375_n150_4color.cnf"
    proof_path = cnf_path.with_suffix(".drat")
    clauses = load_cnf(cnf_path)
    # Direct square tests for every relevant distance; no divisor generator.
    distances = [d for d in range(1, N)
                 if any(square(25 * (2*d)**2 + sign * 6*T*(2*d) + T*T)
                        is not None for sign in (-1, 1))]
    edges = [(i, j) for i, j in combinations(range(N), 2)
             if j-i in distances]
    assert all((i, j) in edges for i, j in combinations(CLIQUE, 2))
    var = lambda vertex, color: 4 * vertex + color + 1
    expected = []
    for i in range(N):
        expected.append(tuple(var(i, color) for color in range(4)))
        expected.extend((-var(i, c), -var(i, d))
                        for c, d in combinations(range(4), 2))
    expected.extend((-var(i, c), -var(j, c))
                    for i, j in edges for c in range(4))
    expected.extend((var(i, c),) for c, i in enumerate(CLIQUE))
    assert Counter(map(frozenset, clauses)) == Counter(map(frozenset, expected))
    additions, deletions = [], 0
    for line in proof_path.read_text(encoding="ascii").splitlines():
        fields = line.split()
        if not fields:
            continue
        if fields[0] == "d":
            deletions += 1
            continue
        values = list(map(int, fields))
        assert values[-1] == 0 and 0 not in values[:-1]
        additions.append(tuple(values[:-1]))
    assert additions == [(-484,), (-43, 574), (574,), ()]
    checked, database = [], list(clauses)
    for learned in additions:
        checked.append(rup(database, learned))
        database.append(learned)

    # Scale u_j=2j/375 to k_j=98j, t=49*375.  Choose a single
    # vertical translation that contains every edge completion.
    physical_t = 49 * T
    relative_columns = [392 * j for j in range(N)]
    base_rows = [294 * j for j in range(N)]
    row_values = base_rows + [r + physical_t for r in base_rows]
    geometries = []
    for i, j in edges:
        candidates = []
        for left_even in (False, True):
            ri = base_rows[i] + (physical_t if left_even else 0)
            rj = base_rows[j] + (0 if left_even else physical_t)
            dx = relative_columns[j] - relative_columns[i]
            length = square(dx*dx + (rj-ri)**2)
            if length is None:
                continue
            assert length % 2 == 1 and (ri+rj-length) % 2 == 0
            lo, hi = (ri+rj-length)//2, (ri+rj+length)//2
            row_values.extend((lo, hi))
            candidates.append((ri, rj, length, lo, hi))
        assert candidates
        geometries.append((i, j, candidates))
    shift = 1 - min(row_values)
    if shift % 2 == 0:
        shift += 1
    h = max(row_values) + shift
    p, q = next_prime(25*h), next_prime(next_prime(25*h))
    modulus = 98*p*q

    def center(a, b):
        assert 1 <= a <= h and a % 2 == 1
        assert 1 <= b <= h and b % 2 == 0
        rp = 4*a*pow(294, -1, p) % p
        rq = 4*b*pow(294, -1, q) % q
        z = rp + p * ((rq-rp)*pow(p, -1, q) % q)
        x = 98*z
        assert 0 <= x < modulus and x % 98 == 0
        assert (3*x-4*a) % p == (3*x-4*b) % q == 0
        return x

    labels = [(a+shift, a+shift+physical_t) for a in base_rows]
    centers = [center(a, b) for a, b in labels]
    assert [x-centers[0] for x in centers] == relative_columns
    rivals = []
    for i, j, candidates in geometries:
        for ri, rj, length, lo, hi in candidates:
            ri, rj, lo, hi = [v+shift for v in (ri, rj, lo, hi)]
            middle = (centers[i] + centers[j])//2
            assert 1 <= lo < hi <= h and (lo-hi) % 2 == 1
            # Check whiteness against every possible complete-F label,
            # through its necessary CRT congruence at this point.
            assert (3*middle-4*lo) % (p if lo % 2 else q) != 0
            assert (3*middle-4*hi) % (p if hi % 2 else q) != 0
            odd, even = (lo, hi) if lo % 2 else (hi, lo)
            owner = center(odd, even)
            assert owner not in (middle, centers[i], centers[j])
            black_diag = {(centers[i], ri), (centers[j], rj)}
            shared = {(middle, lo), (middle, hi)}
            owner_diag = {(owner, lo), (owner, hi)}
            assert len(black_diag | shared) == len(owner_diag | shared) == 4
            assert (centers[i]+centers[j], ri+rj) == (2*middle, lo+hi)
            assert (centers[j]-centers[i])**2+(rj-ri)**2 == length*length
            assert length == hi-lo and centers[i] != centers[j]
            assert ((black_diag | shared) ^ (owner_diag | shared)) == black_diag | owner_diag
            rivals.append({"vertices": [i,j], "black_rows": [ri,rj],
                           "white_rows": [lo,hi], "length": length,
                           "white_column": middle,
                           "owner_label": [odd,even], "owner_column": owner})
    result = {"status": "PASS", "vertices": N, "edges": len(edges),
              "distances": distances, "clique": list(CLIQUE),
              "cnf_variables": 4*N, "cnf_clauses": len(clauses),
              "ignored_deletions": deletions, "rup_checks": checked,
              "height": h, "odd_start": shift, "physical_t": physical_t,
              "primes": [p,q], "columns": centers, "labels": labels,
              "checked_rivals": len(rivals), "rivals": rivals,
              "sha256": {path.name: sha256(path.read_bytes()).hexdigest()
                         for path in (cnf_path, proof_path, Path(__file__))}}
    target = HERE / "crt_chain_nonfourcolorable_independent_check.json"
    target.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in
                      ("status", "vertices", "edges", "cnf_clauses",
                       "height", "odd_start", "physical_t", "primes",
                       "checked_rivals")}))
    print(json.dumps({"rup_propagations": [x["propagations"] for x in checked]}))


if __name__ == "__main__":
    main()
