"""Structured SAT for an h x w blackout with w + q_h points (doubles on K_{A,B} for a given part A,
each edge once, singletons elsewhere). Usage: python rows_sat.py H W PART CAP  (PART: one-based digits
of A, e.g. 246). Writes res_h{H}_w{W}_p{PART}.json in this folder."""
import sys, os, json, time
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'jis', 'scripts')))
import six_row_structured_sat as base
from verify_narrow import collision, mask, rectangles

def main():
    H, W = int(sys.argv[1]), int(sys.argv[2])
    A = tuple(int(c) - 1 for c in sys.argv[3]) if len(sys.argv[3]) < 10 else tuple(int(c) - 1 for c in sys.argv[3].split(','))
    cap = int(sys.argv[4])
    base.ROWS = H
    base.COLLAR = 1 + (H - 1) ** 2 // 4
    B = tuple(r for r in range(H) if r not in A)
    t0 = time.time()
    clauses, n, info, _ = base.encode_a(W, (A, B))
    status, model, dt = base.solve_capped('cadical153', clauses, cap)
    rec = {'h': H, 'w': W, 'A': [a + 1 for a in A], 'status': status, 'solve_s': round(dt), 'enc_s': round(time.time() - t0 - dt)}
    if model is not None:
        pts = {((v - 1) % W, (v - 1) // W) for v in model if 0 < v <= n}
        rec['valid'] = collision(rectangles(H, W), mask(pts, W)) is None
        cols = [''.join(str(y + 1) for y in range(H) if (x, y) in pts) for x in range(W)]
        rec['word'] = ','.join(cols)
        rec['size'] = len(pts)
    print(json.dumps(rec), flush=True)
    json.dump(rec, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'res_h{H}_w{W}_p{sys.argv[3]}.json'), 'w'))


if __name__ == '__main__':
    main()
