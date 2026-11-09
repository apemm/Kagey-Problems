import os
import sys, json
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
from verify_narrow import rectangles, mask, collision
def check(h, word):
    m=len(word); pts=[(x,int(c)-1) for x,w in enumerate(word) for c in w]
    return collision(rectangles(h,m), mask(pts,m)) is None
def collar(h, word):
    W=1+(h-1)**2//4; out={}
    for lr in ('1',str(h)):
        for rr in ('1',str(h)):
            out[(lr,rr)] = check(h, [lr]*W + word + [rr]*W)
    return out
if __name__=='__main__':
    for f in sys.argv[1:]:
        r=json.load(open(f)); w=r['word'].split(','); h=r['h']
        print(f, h, len(w), check(h,w), collar(h,w), flush=True)
