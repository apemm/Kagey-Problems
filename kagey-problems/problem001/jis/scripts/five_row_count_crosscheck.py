"""Cross-check of the five-row optimum counts: run the window dynamic programme of
row_bound_count_dp.py (stored presentations recomputed from the window, carried ones kept)
at one width in a child process with a hard wall-clock cap, and record the count or
'unresolved'. Compared afterwards with five_row_optima_dp.py (a separately written transfer
count) at the same width.

Usage: python five_row_count_crosscheck.py HEIGHT WIDTH [--minutes 30] [--out FILE]
"""
import argparse
import json
import multiprocessing as mp
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(HERE, '..', 'data')


def worker(h, m, q):
    sys.path.insert(0, HERE)
    import row_bound_count_dp
    total, detail = row_bound_count_dp.count_row_bound_optima(h, m)
    q.put((total, detail))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('height', type=int)
    ap.add_argument('width', type=int)
    ap.add_argument('--minutes', type=float, default=30.0)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    h, m = args.height, args.width
    t0 = time.time()
    q = mp.Queue()
    proc = mp.Process(target=worker, args=(h, m, q))
    proc.start()
    proc.join(timeout=60 * args.minutes)
    rec = {'height': h, 'width': m, 'method': 'window dynamic programme (row_bound_count_dp.py)',
           'wall_cap_minutes': args.minutes, 'python_version': sys.version.split()[0]}
    if proc.is_alive():
        proc.terminate()
        proc.join()
        rec.update({'status': 'unresolved: wall-clock cap reached', 'count': None})
    else:
        try:
            total, detail = q.get(timeout=5)
            rec.update({'status': 'complete', 'count': total, 'per_partition': detail})
        except Exception:
            rec.update({'status': 'unresolved: no result returned', 'count': None})
    rec['seconds'] = round(time.time() - t0, 2)
    out = args.out or os.path.join(DATA_DIR, f'five_row_count_crosscheck_h{h}_w{m}.json')
    with open(out, 'w') as f:
        json.dump(rec, f, indent=1)
    print(f'h={h} m={m}: {rec["count"]} ({rec["status"]}, {rec["seconds"]} s) -> {out}')


if __name__ == '__main__':
    mp.freeze_support()
    main()
