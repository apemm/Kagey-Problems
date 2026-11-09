"""Bounded witness search for an append-only singleton transition to a constant tail."""
from functools import lru_cache
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision
from verify_seven_thirteen import side_rectangles
from equality_collar_probe import black_mask


@lru_cache(None)
def geometry(w): return rectangles(7,w)


def valid(word): return collision(geometry(len(word)),black_mask(word)) is None


def main():
    source=HERE.parents[1]/'2026-11-07/data/res_h7_w21_p246.json'
    core=tuple(json.loads(source.read_text())['word'].split(','))
    cap=float(sys.argv[1]) if len(sys.argv)>1 else 90
    beam=int(sys.argv[2]) if len(sys.argv)>2 else 64
    begun=time.monotonic();states=[core];checked=0;levels=[];found=None
    for depth in range(19):
        next_states=[]
        for word in states:
            if time.monotonic()-begun>=cap:break
            for row in ('1','7','2','6','3','5','4'):
                padded=word+(row,)*36;checked+=1
                if valid(padded):
                    assert set(geometry(len(padded)))==side_rectangles(7,len(padded))
                    found={'transition':list(word[len(core):]),'tail_row':int(row),
                           'checked_word':','.join(padded),'width':len(padded),
                           'black_cells':black_mask(padded).bit_count(),
                           'presentations_checked':len(geometry(len(padded)))}
                    break
            if found:break
            for row in ('1','7','2','6','3','5','4'):
                candidate=word+(row,);checked+=1
                if valid(candidate):next_states.append(candidate)
        levels.append({'depth':depth,'input_states':len(states),'next_states':len(next_states)})
        print(json.dumps(levels[-1]),flush=True)
        if found or time.monotonic()-begun>=cap or not next_states:break
        # A heuristic truncation affects only witness discovery, never an UNSAT conclusion.
        states=next_states[:beam]
    out={'status':'witness' if found else 'no_witness_in_bounded_search',
         'height':7,'core_width':len(core),'core_word':','.join(core),'collar_memory':36,
         'cap_seconds':cap,'beam_width':beam,'checks':checked,'levels':levels,
         'seconds':time.monotonic()-begun,'witness':found}
    (HERE/'equality_width21_tail_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
