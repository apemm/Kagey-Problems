"""Enumerate all axis-valid 18-point column multisets on seven by nine.

The structural proof excludes empty columns and columns of size four.
If t columns have size three, precisely t are singletons and 9-2t
are double columns. The pair shadow test excludes incidence 4/6-cycles.
"""
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json
import time

HERE = Path(__file__).resolve().parent


def masks(size):
    return [sum(1 << r for r in c) for c in combinations(range(7), size)]


def reflected(mask):
    return sum(1 << (6-r) for r in range(7) if mask & (1 << r))


def add(adj, mask):
    rows = [r for r in range(7) if mask & (1 << r)]
    if any((adj[a] & (1 << b)) or (adj[a] & adj[b])
           for a,b in combinations(rows,2)):
        return None
    new = adj.copy()
    for r in rows:
        new[r] |= mask ^ (1 << r)
    return new


def main():
    started = time.monotonic()
    pairs, triples = masks(2), masks(3)
    patterns = set()
    nonsingletons = [0]*5
    for t in range(5):
        d = 9-2*t
        singletons = list(combinations_with_replacement(masks(1),t))

        def choose_pairs(start, left, adj, columns):
            if not left:
                nonsingletons[t] += 1
                for singles in singletons:
                    p = tuple(sorted(columns + list(singles)))
                    pr = tuple(sorted(map(reflected,p)))
                    patterns.add(min(p,pr))
                return
            for i in range(start,len(pairs)-left+1):
                new = add(adj,pairs[i])
                if new is not None:
                    choose_pairs(i+1,left-1,new,columns+[pairs[i]])

        def choose_triples(start,left,adj,columns):
            if not left:
                choose_pairs(0,d,adj,columns)
                return
            for i in range(start,len(triples)-left+1):
                new = add(adj,triples[i])
                if new is not None:
                    choose_triples(i+1,left-1,new,columns+[triples[i]])

        choose_triples(0,t,[0]*7,[])
        print(json.dumps({'triples':t,'nonsingleton_families':nonsingletons[t],
                          'representatives_so_far':len(patterns)}),flush=True)

    data = json.loads((HERE/'seven_nine_search_data.json').read_text())
    data.update(black_points=18,output_tag='seven_nine_eighteen',
                patterns=sorted(patterns),
                all_axis_patterns=sum(nonsingletons[t]*len(list(
                    combinations_with_replacement(masks(1),t))) for t in range(5)),
                nonsingleton_families_by_triple_count=nonsingletons,
                vertical_reflection_representatives=len(patterns),
                elapsed_seconds=time.monotonic()-started)
    (HERE/'seven_nine_eighteen_data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('patterns','templates_by_last_column')}))


if __name__ == '__main__':
    main()
