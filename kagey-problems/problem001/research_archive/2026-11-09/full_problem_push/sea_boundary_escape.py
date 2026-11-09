"""Measure exact escape to constant seas using restricted row alphabets."""
import argparse
import json
from pathlib import Path
import struct
import time
import numpy as np


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('report', type=Path)
    parser.add_argument('--alphabet', action='append', required=True)
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    assert report['complete']
    graph = args.report.with_suffix('.bin')
    with graph.open('rb') as source:
        magic, h, n = struct.unpack('<iii', source.read(12))
    assert magic == 0x53454731 and n == report['states']
    edges = np.memmap(graph, mode='r', dtype='<i4', offset=12, shape=(n,h))
    component = np.memmap(str(graph)+'.components', mode='r', dtype='<i4', offset=4, shape=(n,))
    results = []
    for encoded in args.alphabet:
        started = time.monotonic()
        rows = sorted(set(map(int, encoded.split(','))))
        assert rows and min(rows) >= 1 and max(rows) <= h
        roots = [report['components']['constant_states'][r-1] for r in rows]
        roots = [v for v in roots if v >= 0]
        reached = np.zeros(n, dtype=np.bool_)
        reached[roots] = True
        history = [len(roots)]
        while True:
            changed = 0
            for start in range(0,n,250000):
                stop = min(n,start+250000)
                ids = np.flatnonzero(~reached[start:stop])+start
                if not len(ids):
                    continue
                hit = np.zeros(len(ids), dtype=np.bool_)
                for r in rows:
                    target = np.asarray(edges[ids,r-1])
                    hit |= (target >= 0) & reached[np.maximum(target,0)]
                new = ids[hit]
                reached[new] = True
                changed += len(new)
            history.append(int(reached.sum()))
            if not changed:
                break
        cyclic = []
        for item in report['components']['cyclic_components']:
            mask = component == item['id']
            cyclic.append(dict(component=item['id'], size=item['size'],
                               escaping=int(np.count_nonzero(reached & mask))))
        result = dict(rows=rows, roots=roots, reached=int(reached.sum()),
                      total_states=n, cyclic=cyclic, pass_counts=history,
                      seconds=time.monotonic()-started)
        results.append(result)
        print(json.dumps(result), flush=True)
    output = args.report.with_suffix('.escape.json')
    output.write_text(json.dumps(dict(graph=graph.name,results=results),indent=2)+'\n')


if __name__ == '__main__':
    main()
