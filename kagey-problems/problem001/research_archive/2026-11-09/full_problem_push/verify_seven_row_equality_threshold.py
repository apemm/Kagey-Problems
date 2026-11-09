"""Independent row-graph and completed-range checks for equality-width exclusions."""
from pathlib import Path
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
from verify_seven_fourteen import triangle_free_graphs
from verify_seven_thirteen import side_rectangles
from verify_narrow import rectangles, collision


def main():
    begin = time.monotonic()
    graphs = triangle_free_graphs(12)
    assert len(graphs) == 35
    def reflect(mask):
        return sum(1 << (6-r) for r in range(7) if mask >> r & 1)
    canonical = sorted({min(g, tuple(sorted(map(reflect, g)))) for g in graphs})
    assert len(canonical) == 19
    base = json.loads((HERE/'equality_window_capacity_check.json').read_text())
    assert base['status'] == 'PASS' and base['seven_row_equality_width_lower_bound'] == 17
    completed = []; witnesses = []; records = []
    for filename in sorted(HERE.glob('equality_h7_w*_0_19_cadical195.json')):
        data = json.loads(filename.read_text()); w = data['width']
        assert data['height'] == 7 and data['target'] == w+12
        assert data['start_index'] == 0 and data['end_exclusive'] == 19
        assert [tuple(r['masks']) for r in data['cores']] == canonical
        assert all(r['empty_columns'] == 0 for r in data['cores'])
        assert data['crop_black_bounds'] == {'9':17,'10':18,'11':20,'12':21,'13':22,'14':23}
        for name, digest in data['source_sha256'].items():
            assert hashlib.sha256((HERE/name).read_bytes()).hexdigest() == digest
        indices = [r['index'] for r in data['results']]
        assert indices == list(range(len(indices)))
        statuses = [r['status'] for r in data['results']]
        if data['status'] == 'UNSAT_range':
            assert indices == list(range(19)) and statuses == ['UNSAT']*19
            completed.append(w)
        for result in data['results']:
            if result['status'] != 'SAT': continue
            word = result['column_word'].split(',')
            assert len(word) == w
            black = sum(1 << ((int(r)-1)*w+c) for c,col in enumerate(word) for r in col)
            assert hex(black) == result['black_hex'] and black.bit_count() == w+12
            rects = rectangles(7,w)
            assert set(rects) == side_rectangles(7,w) and collision(rects,black) is None
            doubles = [sum(1 << (int(r)-1) for r in col) for col in word if len(col)==2]
            assert len(doubles)==12 and sorted(doubles)==list(canonical[result['index']])
            witnesses.append({'width':w,'column_word':result['column_word'],
                              'presentations':len(rects)})
        records.append({'file':filename.name,'sha256':hashlib.sha256(filename.read_bytes()).hexdigest(),
                        'width':w,'status':data['status'],'completed_cores':len(indices),
                        'search_seconds':data['wall_seconds']})
    lower = 17
    while lower in completed: lower += 1
    tail = json.loads((HERE/'seven_row_equality_tail_check.json').read_text())
    assert tail['status']=='PASS' and tail['all_widths_from']==21
    assert lower<=21
    exact_twenty = None
    if 20 in completed:
        word='36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23'.split(',')
        black=sum(1<<((int(r)-1)*20+c) for c,col in enumerate(word) for r in col)
        rects=rectangles(7,20)
        assert black.bit_count()==31 and set(rects)==side_rectangles(7,20)
        assert collision(rects,black) is None
        exact_twenty={'value':31,'column_word':','.join(word),'presentations':len(rects)}
    out = {'status':'PASS','raw_triangle_free_twelve_edge_graphs':35,
           'reflection_classes':19,'excluded_equality_widths':completed,
           'seven_row_equality_width_lower_bound':lower,'all_widths_from':21,
           'exact_equality_threshold':21 if lower==21 else None,
           'f_7_20':exact_twenty,'witnesses':witnesses,
           'runs':records,'verification_seconds':time.monotonic()-begin}
    (HERE/'seven_row_equality_threshold_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__': main()
