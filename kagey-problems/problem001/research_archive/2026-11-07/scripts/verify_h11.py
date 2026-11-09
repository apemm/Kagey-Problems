import sys, json, os
import os; sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
from verify_narrow import rectangles, mask, collision
r = json.load(open(sys.argv[1])); h = r['h']; order = [tuple(e) for e in r['order']]
toks = r['word'].split(','); it = iter(order); cols = []
for t in toks:
    if t in ('1', str(h)): cols.append((int(t),))
    else:
        e = next(it); assert ''.join(map(str, e)) == t, (t, e); cols.append(e)
assert next(it, None) is None
def check(cs):
    m = len(cs); pts = [(x, r - 1) for x, c in enumerate(cs) for r in c]
    return collision(rectangles(h, m), mask(pts, m)) is None
W = 1 + (h - 1) ** 2 // 4
print('h', h, 'width', len(cols), 'points', sum(map(len, cols)), 'core valid', check(cols), flush=True)
for L in (1, h):
    for R in (1, h):
        print('pads', L, R, check([(L,)] * W + cols + [(R,)] * W), flush=True)
if len(sys.argv) > 2:
    for side in ('L', 'R'):
        for v in (1, h):
            k = 0
            while k < W:
                k += 1
                cs = [(v,)] * k + cols if side == 'L' else cols + [(v,)] * k
                if not check(cs): break
            else:
                k += 1
            print('side', side, 'row', v, 'first failing pad', k if k <= W else None, flush=True)
