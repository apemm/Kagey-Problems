"""Combine bounded core runs and independently check all finite witnesses."""
from pathlib import Path
import hashlib
import json
from collections import defaultdict
import time

from verify_seven_fourteen import triangle_free_graphs
from verify_narrow import rectangles,collision
from verify_seven_thirteen import side_rectangles

HERE=Path(__file__).resolve().parent


def main():
    begun=time.monotonic()
    def reflect(mask):return sum(1<<(6-r) for r in range(7) if mask>>r&1)
    cores=[]
    for edge_count in (11,12):
        graphs=triangle_free_graphs(edge_count)
        assert len(graphs)==(420 if edge_count==11 else 35)
        reps=sorted({min(g,tuple(sorted(map(reflect,g)))) for g in graphs})
        cores.extend({'empty_columns':edge_count-11,'masks':list(g)} for g in reps)
    assert len(cores)==229
    threshold=json.loads((HERE/'seven_row_equality_threshold_check.json').read_text())
    assert threshold['exact_equality_threshold']==21
    unsat=defaultdict(set);sat=defaultdict(list);sources=[];uses_fifteen=False;uses_sixteen=False
    for path in sorted(HERE.glob('deficit_one_h7_w*.json')):
        data=json.loads(path.read_text());w=data['width']
        assert 15<=w<=19 and data['height']==7 and data['target']==w+11
        assert data['cores']==cores
        crops={int(k):v for k,v in data['known_crop_bounds'].items()}
        base_crops={9:17,10:18,11:20,12:21,13:22,14:24}
        assert crops in (base_crops,{**base_crops,15:25},{**base_crops,15:25,16:26})
        if 15 in crops:
            assert w>15
            uses_fifteen=True
        if 16 in crops:
            assert w>16
            uses_sixteen=True
        for name,digest in data['source_sha256'].items():
            assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==digest
        seen=set()
        for result in data['results']:
            index=result['index'];assert 0<=index<229 and index not in seen;seen.add(index)
            if result['status']=='UNSAT':unsat[w].add(index)
            elif result['status']=='SAT':
                word=result['column_word'].split(',');assert len(word)==w
                black=sum(1<<((int(r)-1)*w+c) for c,col in enumerate(word) for r in col if r!='0')
                rects=rectangles(7,w)
                assert black.bit_count()==w+11 and hex(black)==result['black_hex']
                assert set(rects)==side_rectangles(7,w) and collision(rects,black) is None
                sat[w].append({'index':index,'column_word':result['column_word'],'presentations':len(rects)})
        sources.append({'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                        'width':w,'completed_unsat':sum(r['status']=='UNSAT' for r in data['results']),
                        'wall_seconds':data['wall_seconds']})
    if uses_fifteen:assert len(unsat[15])==229
    if uses_sixteen:assert len(unsat[16])==229
    lower=json.loads((HERE/'seven_row_triple_extensions.json').read_text())['results']
    bywidth={r['width']:r for r in lower}
    summary=[]
    for w in range(15,20):
        assert not any(r['index'] in unsat[w] for r in sat[w])
        exact=None;word=None;presentations=None
        if sat[w]:
            exact=w+11;word=sat[w][0]['column_word'];presentations=sat[w][0]['presentations']
        elif len(unsat[w])==229:
            exact=w+10;word=bywidth[w]['column_words'][0]
            cols=word.split(',');black=sum(1<<((int(r)-1)*w+c) for c,col in enumerate(cols) for r in col)
            rects=rectangles(7,w)
            assert black.bit_count()==exact and collision(rects,black) is None
            assert set(rects)==side_rectangles(7,w)
            presentations=len(rects)
        summary.append({'width':w,'excluded_core_count':len(unsat[w]),'all_cores_excluded':len(unsat[w])==229,
                        'exact_value':exact,'witness':word,'witness_presentations':presentations,'sat_records':sat[w]})
    out={'status':'PASS','core_count':229,'raw_eleven_edge_graphs':420,'raw_twelve_edge_graphs':35,
         'widths':summary,'sources':sources,'seconds':time.monotonic()-begun,
         'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'seven_row_deficit_one_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='sources'}))


if __name__=='__main__':main()
