"""Known valid filled boards satisfy every pinned-fiber clause under fixed cells."""
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from pysat.solvers import Solver
from single_cell_extension_constraints import unary_constraints
from pinned_sea_fiber_sat import encode


def main():
    records=[]
    for source in ('constant_sea_h7_cadical195_seed17.json',
                   'constant_sea_h9_cadical195_seed18_odd57.json'):
        start=time.monotonic();saved=json.loads((HERE/source).read_text());h=saved['height']
        witness=next(e for e in saved['events'] if e.get('status')=='SAT');filled=witness['columns_one_based']
        core=[C if len(C)==2 else [] for C in filled];w=len(core)
        points=[(x,r-1) for x,C in enumerate(core) for r in C]
        bad,_,_=unary_constraints(h,w,points)
        name=f'fiber_calibration_h{h}_source.json'
        (HERE/name).write_text(json.dumps({'height':h,'events':[{'status':'SAT','columns_one_based':core}]})+'\n')
        domains={x:[r+1 for r in range(h) if r*w+x not in bad] for x,C in enumerate(core) if not C}
        (HERE/f'fiber_calibration_h{h}_source_unary.json').write_text(json.dumps({'all_row_domains':domains})+'\n')
        clauses,cell,_,info=encode(name,True);assumptions=[]
        for (x,r),v in cell.items():
            actual=r+1 in filled[x]
            if v is True:assert actual
            elif v is False:assert not actual
            else:assumptions.append(v if actual else -v)
        with Solver(name='glucose4',bootstrap_with=clauses) as solver:
            assert solver.solve(assumptions=assumptions)
        records.append({'height':h,'width':w,'status':'PASS','seconds':time.monotonic()-start,**info})
    (HERE/'pinned_sea_fiber_calibration.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(records))


if __name__=='__main__':main()
