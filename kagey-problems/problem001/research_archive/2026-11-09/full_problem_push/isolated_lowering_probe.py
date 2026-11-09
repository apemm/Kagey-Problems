"""Bounded periodic test of a sufficient condition for internal greedy reset.

The test uses the exact positive-support language, not finite-prefix validity.
A replacement changes one actual column, not every column of its phase.
"""
from itertools import product
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import time

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'2026-11-08/dominance_bridge/sea_sparse_automaton.py'
spec=importlib.util.spec_from_file_location('lowering_sea_source',SOURCE)
sea=importlib.util.module_from_spec(spec);spec.loader.exec_module(sea)


def main():
    h=int(sys.argv[1]) if len(sys.argv)>1 else 7
    maxperiod=int(sys.argv[2]) if len(sys.argv)>2 else 4
    start=time.monotonic()
    patterns,stats=sea.forbidden_patterns(h,time.monotonic()+120)
    output=[]
    for period in range(1,maxperiod+1):
        # Each periodic embedding retains all actual roles. In particular two
        # distinct positions with the same phase remain separate comparisons.
        embedded=[tuple(((s+x)%period,r,x+s) for x,r in P)
                  for P in patterns for s in range(period)]
        accepted=0;frozen=[]
        for word in product(range(1,h+1),repeat=period):
            blocked=[set() for _ in word]
            valid=True
            for P in embedded:
                mismatch=None
                for phase,row,column in P:
                    if word[phase]!=row:
                        if mismatch is not None:break
                        mismatch=(phase,row,column)
                else:
                    if mismatch is None:
                        valid=False;break
                    phase,row,column=mismatch
                    if row<word[phase]:blocked[phase].add(row)
            if not valid:continue
            accepted+=1
            if any(row>1 for row in word) and all(
                    all(r in blocked[i] for r in range(1,row))
                    for i,row in enumerate(word)):
                witnesses=[]
                for i,row in enumerate(word):
                    for target in range(1,row):
                        for P in embedded:
                            mismatches=[(ph,r,x) for ph,r,x in P if word[ph]!=r]
                            if len(mismatches)==1 and mismatches[0][:2]==(i,target):
                                x0=mismatches[0][2]
                                witnesses.append({'phase':i,'target':target,
                                    'support_relative_to_changed_column':[[x-x0,r] for _,r,x in P]})
                                break
                frozen.append({'word':word,'blocking_supports':witnesses})
        record={'period':period,'accepted':accepted,'frozen_count':len(frozen),
                'first_frozen':frozen[:5]}
        output.append(record);print(json.dumps(record),flush=True)
        if frozen:break
    result={'height':h,'maxperiod_requested':maxperiod,'geometry':stats,'periods':output,
            'seconds':time.monotonic()-start,
            'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest()}
    (HERE/f'isolated_lowering_h{h}_p{maxperiod}.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
