"""Verify the full axis-core catalog, projected counts, and all eight optima."""
from itertools import combinations,product
from pathlib import Path
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision
from verify_seven_thirteen import side_rectangles
from verify_seven_fourteen import triangle_free_graphs
from verify_equality_window_capacity import load_completed


def row_reflection(mask):
    return sum(1<<(6-r) for r in range(7) if mask>>r&1)


def canonical(core):
    core=tuple(sorted(core))
    return min(core,tuple(sorted(map(row_reflection,core))))


def independent_catalog():
    types={}
    types['ten_doubles']={(canonical(core),0) for core in triangle_free_graphs(10)}
    types['eleven_doubles_empty']={(canonical(core),1) for core in triangle_free_graphs(11)}
    triples=set()
    raw=set()
    for inside in combinations(range(7),3):
        outside=[r for r in range(7) if r not in inside]
        for left in combinations(outside,2):
            if outside[0] not in left:
                continue
            right=[r for r in outside if r not in left]
            outer=[(1<<a)|(1<<b) for a in left for b in right]
            for colors in product(inside,repeat=4):
                color=dict(zip(outside,colors))
                if any(color[a]==color[b] for a in left for b in right):
                    continue
                core=tuple(sorted([sum(1<<r for r in inside)]+outer+
                                  [(1<<r)|(1<<color[r]) for r in outside]))
                raw.add(core)
                triples.add((canonical(core),0))
    assert len(raw)==1890 and len(triples)==957
    types['one_triple']=triples
    assert [len(types[k]) for k in ('ten_doubles','eleven_doubles_empty','one_triple')]==[1497,210,957]
    return set.union(*types.values()),{k:len(v) for k,v in types.items()}


def transform(black,horizontal=False,vertical=False):
    out=0
    for r in range(7):
        for c in range(13):
            if black>>(r*13+c)&1:
                rr=6-r if vertical else r
                cc=12-c if horizontal else c
                out|=1<<(rr*13+cc)
    return out


def word(black):
    return ','.join(''.join(str(r+1) for r in range(7) if black>>(r*13+c)&1)
                    for c in range(13))


def main():
    began=time.monotonic()
    records=json.loads((HERE/'fixed_excess_ten_cores.json').read_text())['cores']
    independent,counts=independent_catalog()
    actual={(tuple(r['masks']),r['empty_columns']) for r in records}
    assert independent==actual and len(records)==len(actual)==2664
    solved,sources=load_completed('fixed_core_h7_w13_*cadical195*.json',13,23)
    remaining={996,998,999}
    assert all(solved.get(i)=='UNSAT' for i in range(2664) if i not in remaining)
    data=[]
    for method in ('compact','fiber'):
        path=HERE/f'seven_thirteen_optimum_count_{method}.json'
        d=json.loads(path.read_text())
        assert d['status']=='complete' and d['indices']==[996,998,999]
        assert [r['index'] for r in d['completed_cores']]==[996,998,999]
        assert [(r['index'],r['models']) for r in d['completed_cores']]==[(996,1),(998,0),(999,1)]
        data.append(d)
        sources.append(dict(name=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    models=[{(r['index'],int(r['black_hex'],16)) for r in d['models']} for d in data]
    assert models[0]==models[1] and len(models[0])==2
    rects=rectangles(7,13)
    assert set(rects)==side_rectangles(7,13)
    all_boards=set()
    representatives=[]
    for index,B in sorted(models[0]):
        columns=[sum(1<<r for r in range(7) if B>>(r*13+c)&1) for c in range(13)]
        core=records[index]['masks']
        assert sorted(mask for mask in columns if mask.bit_count()>=2)==core
        assert columns.index(core[0])<6
        assert tuple(core)!=tuple(sorted(map(row_reflection,core)))
        orbit={transform(B,h,v) for h in (False,True) for v in (False,True)}
        assert len(orbit)==4 and not all_boards&orbit
        all_boards|=orbit
        representatives.append(dict(index=index,column_word=word(B),orbit_size=4))
    assert len(all_boards)==8
    for B in all_boards:
        assert B.bit_count()==23 and collision(rects,B) is None
    out=dict(status='PASS',height=7,width=13,maximum_black_points=23,
             exact_maximum_blackout_count=8,reflection_orbits=2,
             independent_core_counts=counts,total_cores=2664,
             excluded_cores=2661,remaining_core_projected_counts={996:1,998:0,999:1},
             rectangle_count=len(rects),representatives=representatives,
             all_eight_column_words=[word(B) for B in sorted(all_boards)],
             sources=sources,seconds=time.monotonic()-began)
    (HERE/'seven_thirteen_optimum_count_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sources','all_eight_column_words')}))


if __name__=='__main__':
    main()
