"""Verify the width14 witness, full coverage, and an independent row-graph catalog."""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,mask,collision
from verify_seven_thirteen import side_rectangles
from fixed_excess_eleven_sat import catalog


def triangle_free_graphs(edge_count):
    edges=list(combinations(range(7),2));out=set()
    for chosen in combinations(range(21),edge_count):
        neighbors=[0]*7;good=True
        for e in chosen:
            a,b=edges[e]
            if neighbors[a]&neighbors[b]:good=False;break
            neighbors[a]|=1<<b;neighbors[b]|=1<<a
        if good:out.add(tuple(sorted((1<<edges[e][0])|(1<<edges[e][1]) for e in chosen)))
    return out


def main():
    began=time.monotonic()
    word='7,56,45,34,23,2,12,1,2,3,14,25,367,17'
    columns=[tuple(map(int,C)) for C in word.split(',')]
    B=mask([(x,r-1) for x,C in enumerate(columns) for r in C],14)
    rects=rectangles(7,14)
    assert set(rects)==side_rectangles(7,14)
    assert B.bit_count()==24 and collision(rects,B) is None
    all_graphs={e:triangle_free_graphs(e) for e in (11,12)}
    assert len(all_graphs[11])==420 and len(all_graphs[12])==35
    reflect=lambda mask:sum(1<<(6-r) for r in range(7) if mask>>r&1)
    representatives=set()
    for e,graphs in all_graphs.items():
        for graph in graphs:
            image=tuple(sorted(map(reflect,graph)))
            representatives.add((e-11,min(graph,image)))
    actual={(r['empty_columns'],tuple(r['masks'])) for r in catalog()}
    assert representatives==actual and len(actual)==229
    source=HERE/'fixed_core_h7_w14_0_cadical195.json'
    run=json.loads(source.read_text())
    assert run['status']=='UNSAT_range' and run['start_index']==0 and run['end_exclusive']==229
    assert [r['index'] for r in run['results']]==list(range(229))
    assert all(r['status']=='UNSAT' for r in run['results'])
    out={'status':'PASS','height':7,'width':14,'exact_value':24,'column_word':word,
         'rectangles':len(rects),'distinct_presentations':len(rects),
         'raw_triangle_free_graph_counts':{e:len(g) for e,g in all_graphs.items()},
         'reflection_core_count':len(actual),'completed_unsat_cores':len(run['results']),
         'search_seconds':run['wall_seconds'],'source':source.name,
         'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'verification_seconds':time.monotonic()-began}
    (HERE/'seven_fourteen_exact_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
