"""Exact pinned-order sea filling with compact axis rivals and tilted fibers."""
from collections import Counter,defaultdict
from itertools import combinations
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from constant_sea_order_sat import shapes
from verify_sparse_board import weak_rectangles


def encode(source,odd,guarded=False,allowed_rows=None,point_guards=False):
    from pysat.card import CardEnc,EncType
    from pysat.formula import IDPool
    saved=json.loads((HERE/source).read_text());h=saved['height']
    found=next(e for e in saved['events'] if e.get('status') in ('SAT','CANDIDATE'))
    assert found.get('status')=='SAT' or saved.get('skip_unary_domains',False)
    core=[{r-1 for r in C} for C in found['columns_one_based']];w=len(core)
    assert all(len(C)<=2 for C in core)
    if guarded or saved.get('skip_unary_domains',False):
        domain={x:set(range(0,h,2) if odd else range(h)) for x,C in enumerate(core) if not C}
    else:
        unary=json.loads((HERE/(Path(source).stem+'_unary.json')).read_text())
        domain={int(x):{r-1 for r in rows if not odd or r%2} for x,rows in unary['all_row_domains'].items()}
    if allowed_rows is not None:
        allowed={r-1 for r in allowed_rows}
        assert all(0<=r<h for r in allowed)
        domain={x:rows&allowed for x,rows in domain.items()}
    pool=IDPool();clauses=[];cell={};guards={}
    for x in range(w):
        if core[x]:
            if guarded:
                if point_guards:
                    for r in core[x]:guards[r*w+x]=pool.id(('pointguard',x,r))
                else:guards[x]=pool.id(('guard',x))
            for r in range(h):
                cell[x,r]=(guards[r*w+x if point_guards else x] if guarded else True) if r in core[x] else False
        else:
            variables=[]
            for r in range(h):
                cell[x,r]=pool.id(('cell',x,r)) if r in domain[x] else False
                if r in domain[x]:variables.append(cell[x,r])
            if variables:clauses+=CardEnc.equals(variables,1,vpool=pool,encoding=EncType.seqcounter).clauses
            else:clauses.append([])
    positive_clauses=set();flags={};pair_groups=defaultdict(list);point_groups=defaultdict(list)
    def support(points):
        variables=set();seen={}
        for x,r in points:
            value=cell[x,r]
            if value is False:return None
            if value is True:continue
            if not core[x] and x in seen and seen[x]!=r:return None
            seen[x]=r;variables.add(value)
        return tuple(sorted(variables))
    def forbid(points):
        values=support(points)
        if values is not None:positive_clauses.add(tuple(-v for v in values))
    def flag(values):
        if values is None:return False
        if not values:return True
        if len(values)==1:return values[0]
        if values not in flags:
            value=pool.id(('conjunction',values));flags[values]=value
            clauses.append([-v for v in values]+[value])
            clauses.extend([-value,v] for v in values)
        return flags[values]
    potential=[C if C else domain[x] for x,C in enumerate(core)]
    total=active=0
    for shape in shapes(h):
        span=max(x for x,r in shape)
        for left in range(w-span):
            total+=1
            R=tuple((left+x,r) for x,r in shape)
            if sum(cell[p] is not False for p in R)<2:continue
            active+=1;forbid(R)
            for k,p in enumerate(R):
                rest=R[:k]+R[k+1:]
                values=support(rest)
                if values is not None:
                    point_groups[p].append(flag(values))
                    x,r=p
                    for t in potential[x]:
                        if (r-t)%2:forbid(rest+((x,t),))
            for i,j in combinations(range(4),2):
                p,q=R[i],R[j];remaining=tuple(R[k] for k in range(4) if k not in (i,j))
                values=support(remaining)
                if values is None:continue
                pair_groups[tuple(sorted((p,q)))].append(flag(values))
                x,r=p;z,s=q
                if x==z:
                    if (r-s)%2:forbid(remaining)
                elif r==s:
                    for t in potential[x]&potential[z]:forbid(remaining+((x,t),(z,t)))
                else:forbid(remaining+((x,s),(z,r)))
    clauses.extend(list(C) for C in positive_clauses)
    def amo(values):
        constants=sum(v is True for v in values)
        counts=Counter(v for v in values if v is not True)
        if constants>1:clauses.append([]);return
        if constants:
            clauses.extend([-v] for v in counts);return
        repeated=[v for v,count in counts.items() if count>1]
        clauses.extend([-v] for v in repeated)
        unique=[v for v,count in counts.items() if count==1]
        if len(unique)>1:
            clauses.extend(CardEnc.atmost(unique,1,vpool=pool,encoding=EncType.seqcounter).clauses)
    for group in pair_groups.values():amo(group)
    for group in point_groups.values():amo(group)
    return clauses,cell,core,{'height':h,'width':w,'odd_rows_only':odd,'variables':pool.top,
        'clauses':len(clauses),'tilted_rectangles':total,'potentially_weak_tilts':active,
        'positive_axis_and_hidden_supports':len(positive_clauses),'conjunction_flags':len(flags),
        'pair_fibers':len(pair_groups),'point_fibers':len(point_groups),
        'minimum_domain':min(map(len,domain.values())),'guard_variables':guards,
        'point_guards':point_guards,'allowed_rows':allowed_rows}


def worker(send,source,odd,solver_name,guarded,allowed_rows,minimize,point_guards):
    try:
        from pysat.solvers import Solver
        start=time.monotonic();clauses,cell,core,info=encode(source,odd,guarded,allowed_rows,point_guards)
        send.send({'event':'encoded','encoding_seconds':time.monotonic()-start,**info})
        with Solver(name=solver_name,bootstrap_with=clauses) as solver:
            phases=[]
            for (x,r),value in cell.items():
                if value is not True and value is not False:phases.append(value if r==0 else -value)
            solver.set_phases(phases);sat=solver.solve(assumptions=list(info['guard_variables'].values()))
            result={'event':'result','status':'SAT' if sat else 'UNSAT','seconds':time.monotonic()-start,
                    'info':info,'stats':solver.accum_stats()}
            def pattern(assumed):
                w=info['width']
                if point_guards:
                    return [{'column':p%w,'slot':(p%w)//4,'row':p//w+1}
                            for p,v in info['guard_variables'].items() if v in assumed]
                return [{'column':x,'slot':x//4,'edge':sorted(r+1 for r in core[x])}
                        for x,v in info['guard_variables'].items() if v in assumed]
            if not sat and guarded:
                assumed=set(solver.get_core())
                result['forbidden_partial_order']=pattern(assumed)
                if minimize:
                    send.send(dict(result))
                    for value in sorted(assumed):
                        if value not in assumed:continue
                        trial=sorted(assumed-{value})
                        if not solver.solve(assumptions=trial):
                            assumed=set(solver.get_core())
                            result['forbidden_partial_order']=pattern(assumed)
                            result['seconds']=time.monotonic()-start
                            send.send(dict(result))
                    result['inclusion_minimal_core']=True
                    result['seconds']=time.monotonic()-start;result['stats']=solver.accum_stats()
            if sat:
                model=set(solver.get_model());h=info['height'];w=info['width']
                cols=[[r+1 for r in range(h) if cell[x,r] is True or
                       (cell[x,r] is not False and cell[x,r] in model)] for x in range(w)]
                points=[(x,r-1) for x,C in enumerate(cols) for r in C]
                B=sum(1<<(y*w+x) for x,y in points);seen=set()
                for R in weak_rectangles(h,w,points):
                    P=R&~B;assert P not in seen;seen.add(P)
                result['columns_one_based']=cols
                result['order_one_based']=[sorted(r+1 for r in C) for C in core if len(C)==2]
                result['black_points']=len(points);result['weak_rectangles']=len(seen)
            send.send(result)
    except BaseException:send.send({'event':'error','traceback':traceback.format_exc()})
    finally:send.close()


def main():
    source=sys.argv[1];mode=sys.argv[2];odd=mode=='odd';cap=float(sys.argv[3])
    allowed_rows=None if mode in ('all','odd') else list(map(int,mode.split(',')))
    solver=sys.argv[4] if len(sys.argv)>4 else 'cadical195'
    point_guards='pointguards' in sys.argv[5:]
    guarded='guarded' in sys.argv[5:] or point_guards
    minimize='minimize' in sys.argv[5:]
    receive,send=mp.Pipe(duplex=False);child=mp.Process(target=worker,args=(send,source,odd,solver,guarded,allowed_rows,minimize,point_guards))
    begin=time.monotonic();child.start();send.close();events=[]
    def accept(event):
        events.append(event)
        print(json.dumps({k:v for k,v in event.items() if k!='columns_one_based'}),flush=True)
    while child.is_alive() and time.monotonic()-begin<cap:
        try:
            if receive.poll(min(1,max(0,cap-time.monotonic()+begin))):accept(receive.recv())
        except (EOFError,OSError):break
    if child.is_alive():child.terminate()
    child.join(5)
    while True:
        try:
            if not receive.poll():break
            accept(receive.recv())
        except (EOFError,OSError):break
    final=next((e for e in reversed(events) if e['event'] in ('result','error')),None)
    out={'source':source,'height':json.loads((HERE/source).read_text())['height'],
         'odd_rows_only':odd,'allowed_rows':allowed_rows,'guarded_labels':guarded,'point_guards':point_guards,
         'cap_seconds':cap,'wall_seconds':time.monotonic()-begin,
         'status':final.get('status','error') if final else 'unknown','events':events}
    tag='odd' if odd else 'all'
    if allowed_rows is not None:tag='rows'+'_'.join(map(str,allowed_rows))
    if guarded:tag+='_pointguarded' if point_guards else '_guarded'
    if minimize:tag+='_minimal'
    (HERE/f'pinned_fiber_{Path(source).stem}_{tag}_{solver}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='events'}),flush=True)


if __name__=='__main__':mp.freeze_support();main()
