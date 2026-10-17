"""Recheck of the six-row periodic ansatz: doubles at columns 1, 1+g, ..., 1+8g
(width 8g+1), row-1 singletons in every other column, for gaps g = 1..8 and all
ten row partitions.  Uses the exhaustive column search of six_row_dfs_check.py
with the column types forced, so every edge order is covered.

Usage: python six_row_periodic_check.py OUT.json
Output coordinates are one-based (column, row), (1,1) top left.
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from six_row_dfs_check import partitions, search  # noqa: E402


def main():
    out = sys.argv[1]
    results = []
    t0 = time.time()
    for g in range(1, 9):
        width = 8 * g + 1
        forced = {c: ('double' if (c - 1) % g == 0 else 'single') for c in range(1, width + 1)}
        for idx, part in enumerate(partitions()):
            stats = search(width, part, 1200, forced=forced, max_store=200)
            results.append({'gap': g, 'width': width, 'partition_one_based_rows': [list(part[0]), list(part[1])],
                            'finished': stats['finished'], 'nodes': stats['nodes'],
                            'witnesses_total': stats['witnesses'], 'witnesses': stats['stored'],
                            'seconds': stats['seconds']})
            print(g, width, part, stats['finished'], stats['nodes'], stats['witnesses'], stats['seconds'], flush=True)
    json.dump({'coordinates': 'one-based (column,row), (1,1) top-left', 'results': results,
               'total_seconds': round(time.time() - t0, 1)}, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
