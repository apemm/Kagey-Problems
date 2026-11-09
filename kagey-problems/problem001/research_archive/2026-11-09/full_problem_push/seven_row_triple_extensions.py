"""Direct singleton boundary extensions of the exact width-13 optima."""
from pathlib import Path
import json
import time
from seven_row_boundary_repairs import valid,geometry
from verify_seven_thirteen import side_rectangles

HERE=Path(__file__).resolve().parent


def main():
    begun=time.monotonic();states=set()
    for text in ('56,45,34,23,2,12,1,2,3,14,25,367,17',
                 '567,45,34,23,2,12,1,2,3,14,25,37,17'):
        word=tuple(tuple(map(int,c)) for c in text.split(','))
        reflected=tuple(tuple(sorted(8-r for r in c)) for c in word)
        states.update((word,word[::-1],reflected,reflected[::-1]))
    results=[]
    for w in range(14,20):
        candidates={q for word in states for row in range(1,8)
                    for q in (((row,),)+word,word+((row,),))}
        found=sorted(q for q in candidates if valid(q))
        if found:assert set(geometry(w))==side_rectangles(7,w)
        results.append({'width':w,'black_cells':w+10,'valid_candidates':len(found),
                        'column_words':[','.join(''.join(map(str,c)) for c in word) for word in found[:8]],
                        'presentations':len(geometry(w))})
        if not found:break
        states=set(found[:200])
    out={'status':'direct_witness_search','results':results,'seconds':time.monotonic()-begun}
    (HERE/'seven_row_triple_extensions.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
