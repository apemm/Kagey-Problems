"""Independent check of a board stored as a list of row lists (rows 1..h), with verify_narrow,
plus the collar test (W_h extra columns of each boundary row on each side)."""
import sys, json, os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
from verify_narrow import rectangles, mask, collision
r = json.load(open(sys.argv[1])); h = r['h']; cols = [tuple(c) for c in r['cols']]
def check(cs):
    m = len(cs); return collision(rectangles(h, m), mask([(x, y - 1) for x, c in enumerate(cs) for y in c], m)) is None
print(sys.argv[1], 'h', h, 'width', len(cols), 'points', sum(map(len, cols)), 'excess', sum(map(len, cols)) - len(cols), 'valid', check(cols), flush=True)
