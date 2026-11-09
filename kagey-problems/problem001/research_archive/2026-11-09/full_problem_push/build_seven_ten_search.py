"""Build complete axis candidate families for 19/20 points on 7 by 10."""
from pathlib import Path
from itertools import combinations
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from solver.enumerate import rectangles


def reflect(p):
    return tuple(sorted(sum(1<<(6-r) for r in range(7) if mask>>r&1) for mask in p))


def main():
    target=int(sys.argv[1]) if len(sys.argv)>1 else 20
    assert target in (19,20)
    begin=time.monotonic()
    source='seven_nine_search_data.json' if target==20 else 'seven_nine_eighteen_data.json'
    patterns=set()
    for p in json.loads((HERE/source).read_text())['patterns']:
        for row in range(7):
            q=tuple(sorted(p+[1<<row]))
            patterns.add(min(q,reflect(q)))
    if target==19:
        for p in json.loads((HERE/'seven_nine_search_data.json').read_text())['patterns']:
            q=tuple(sorted(p+[0]))
            patterns.add(min(q,reflect(q)))
    if target==20:
        # At excess ten, a family may also consist of ten double columns.
        # These triangle-free row graphs are not in the triple-core file.
        edges=list(combinations(range(7),2))
        for chosen in combinations(edges,10):
            adj=[0]*7
            good=True
            for a,b in chosen:
                if adj[a]&adj[b]:
                    good=False
                    break
                adj[a]|=1<<b
                adj[b]|=1<<a
            if good:
                q=tuple(sorted((1<<a)|(1<<b) for a,b in chosen))
                patterns.add(min(q,reflect(q)))
    allrects=rectangles(7,10)
    templates=[[] for _ in range(10)]
    for R in allrects:
        if len({x for x,y in R})==2 and len({y for x,y in R})==2:
            continue
        points=sorted((x-1,y-1) for x,y in R)
        templates[max(x for x,y in points)].append([v for p in points for v in p])
    data={'rows':7,'columns':10,'black_points':target,
          'output_tag':f'seven_ten_{target}',
          'patterns':sorted(patterns),'templates_by_last_column':templates,
          'vertical_reflection_representatives':len(patterns),
          'rectangles':len(allrects),'tilted_rectangles':sum(map(len,templates)),
          'elapsed_seconds':time.monotonic()-begin}
    (HERE/f'seven_ten_{target}_data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('patterns','templates_by_last_column')}))


if __name__=='__main__':
    main()
