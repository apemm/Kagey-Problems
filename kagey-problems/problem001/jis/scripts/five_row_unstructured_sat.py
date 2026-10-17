r"""Five rows, unstructured SAT: is there a valid blackout of at least k points?

No structural hypothesis at all.  One variable per grid point; one clause per minimal
symmetric difference D of two distinct rectangles ("D is not entirely black"; a
difference containing a smaller difference is dropped, since its clause is implied);
the cardinality constraint |S| >= k through pysat.card (sequential counter).  This is
the hitting-set formulation of PROBLEM.md convention 4 in SAT form, and it checks the
structured searches without assuming the equality theorem.

For each width the script asks for k = m+5 (expected satisfiable) and k = m+6 (the row
bound), each in a child process with a hard wall-clock cap; an instance that exceeds
the cap is recorded as "unresolved".  Witnesses are rechecked with
verify_narrow.collision.  Rectangles come from verify_narrow.rectangles.

Coordinates in the JSON output are ONE-BASED (column, row), (1, 1) top left.

Usage:
  python five_row_unstructured_sat.py --widths 8 9 10 11 12 --solver cadical153 --cap 1800
                                      --out ../data/five_row_unstructured_cadical153.json
"""
import argparse
import json
import os
import subprocess
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import verify_narrow  # noqa: E402

H = 5


def minimal_differences(rects):
    diffs = set()
    for a, b in combinations(rects, 2):
        diffs.add(a ^ b)
    by_size = sorted(diffs, key=lambda d: d.bit_count())
    kept, sizes, result = set(), set(), []
    for d in by_size:
        size = d.bit_count()
        bits = [1 << i for i in range(d.bit_length()) if d >> i & 1]
        redundant = False
        for s in sorted(sizes):
            if s >= size:
                break
            if any(sum(sub) in kept for sub in combinations(bits, s)):
                redundant = True
                break
        if not redundant:
            kept.add(d)
            sizes.add(size)
            result.append(d)
    return len(diffs), result


def worker(args):
    from pysat.solvers import Solver
    from pysat.card import CardEnc, EncType
    m, k = args.width, args.bound
    n = H * m
    t0 = time.time()
    rects = verify_narrow.rectangles(H, m)
    total, kept = minimal_differences(rects)
    clauses = [[-(i + 1) for i in range(d.bit_length()) if d >> i & 1] for d in kept]
    card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=k, top_id=n,
                           encoding=EncType.seqcounter)
    clauses.extend(card.clauses)
    t_build = time.time() - t0
    t1 = time.time()
    with Solver(name=args.solver, bootstrap_with=clauses) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
    t_solve = time.time() - t1
    result = dict(width=m, bound=k, solver=args.solver, status='SAT' if sat else 'UNSAT',
                  rectangles=len(rects), differences=total, minimal_differences=len(kept),
                  clauses=len(clauses), variables=max(n, card.nv),
                  build_seconds=round(t_build, 2), solve_seconds=round(t_solve, 2))
    if sat:
        pts = sorted(((v - 1) % m, (v - 1) // m) for v in model if 0 < v <= n)  # (col,row)
        black = verify_narrow.mask(pts, m)
        result['witness_size'] = len(pts)
        result['witness_one_based'] = [[c + 1, r + 1] for c, r in pts]
        result['witness_valid_by_verify_narrow'] = verify_narrow.collision(rects, black) is None
        result['witness_picture'] = [''.join('#' if (c, r) in set(pts) else '.'
                                             for c in range(m)) for r in range(H)]
    print(json.dumps(result))


def run_instance(args, m, k):
    cmd = [sys.executable, '-I', os.path.abspath(__file__), '--worker', '--width', str(m),
           '--bound', str(k), '--solver', args.solver]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=args.cap)
    except subprocess.TimeoutExpired:
        return dict(width=m, bound=k, solver=args.solver, status='unresolved',
                    wall_seconds=round(time.time() - t0, 1), cap_seconds=args.cap)
    wall = time.time() - t0
    if proc.returncode != 0:
        return dict(width=m, bound=k, solver=args.solver, status='error',
                    wall_seconds=round(wall, 1), stderr=proc.stderr[-2000:])
    out = json.loads(proc.stdout.strip().splitlines()[-1])
    out['wall_seconds'] = round(wall, 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--widths', type=int, nargs='+', default=list(range(8, 13)))
    ap.add_argument('--excess', type=int, nargs='+', default=[5, 6],
                    help='ask for |S| >= m + e for each e')
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--cap', type=int, default=1800)
    ap.add_argument('--out', default=None)
    ap.add_argument('--worker', action='store_true')
    ap.add_argument('--width', type=int)
    ap.add_argument('--bound', type=int)
    args = ap.parse_args()
    if args.worker:
        worker(args)
        return
    import pysat
    results = dict(method='unstructured hitting-set SAT with cardinality |S| >= k',
                   solver=args.solver, pysat_version=pysat.__version__,
                   python_version=sys.version.split()[0], cap_seconds=args.cap,
                   coordinates='one-based (column,row)', instances=[])
    for m in args.widths:
        for e in args.excess:
            r = run_instance(args, m, m + e)
            results['instances'].append(r)
            print(f"width {m} |S|>={m + e}: {r['status']} wall {r.get('wall_seconds')}s "
                  f"clauses {r.get('clauses')} vars {r.get('variables')} "
                  f"valid {r.get('witness_valid_by_verify_narrow')}", flush=True)
            if args.out:
                with open(args.out, 'w') as f:
                    json.dump(results, f, indent=1)


if __name__ == '__main__':
    main()
