"""Backtracking search for spacing-4 boards in the '1, x, h' family (or the one-switch family), built
left to right. Each rectangle is checked once, when its rightmost column is placed, so a prefix is
extended only if it has no violation. Randomized candidate order with restarts.
Usage: python dfs_gap.py h family seed maxnodes   (family: gap | switch)"""
import sys, random, json, time
from fastcheck import shapes, rival
HARD = False
ADAPT = False
ENDS = set()
FAIL = {}


class Board:
    def __init__(self, h):
        self.h = h
        self.cols = []
        self.seen = {}
        self.F = {frozenset((a, b)) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2}
        self.byright = {}
        for sh in shapes(h):
            span = max(dx for dx, _ in sh)
            self.byright.setdefault(span, []).append(sh)
        self.log = []      # per pushed column: list of presentations added

    def push(self, col):
        """Append a column; return False (and leave it pushed) if a violation completes."""
        self.cols.append(frozenset(col))
        X = len(self.cols) - 1
        added = []
        self.log.append(added)
        ok = True
        for span, shs in self.byright.items():
            x0 = X - span
            if x0 < 0:
                continue
            for sh in shs:
                if max(dx for dx, _ in sh) != span:
                    continue
                cs = [(x0 + dx, r) for dx, r in sh]
                k = [r in self.cols[x] for x, r in cs]
                if sum(k) < 2:
                    continue
                P = frozenset(c for c, kk in zip(cs, k) if not kk)
                if not P or P in self.seen:
                    ok = False
                    break
                self.seen[P] = 1
                added.append(P)
                if rival(P, self.cols, self.F):
                    ok = False
                    break
            if not ok:
                break
        return ok

    def pop(self):
        for P in self.log.pop():
            del self.seen[P]
        self.cols.pop()


def main():
    h, fam, seed, maxn = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    global HARD
    HARD = len(sys.argv) > 5 and sys.argv[5] == 'hard'
    global ADAPT
    ADAPT = len(sys.argv) > 5 and sys.argv[5] == 'adapt'
    lastleft = []
    global ENDS
    if len(sys.argv) > 6:
        ENDS = {tuple(int(c) for c in t.split('-')) for t in sys.argv[6].split(',')}
    rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    q = len(E)
    t0 = time.time()
    best_depth = 0
    nodes = 0
    while True:
        bd = Board(h)
        used = set()
        stack = []      # each frame: list of remaining candidates
        first = [h] if fam == 'gap' else ([rng.choice((1, h))] if fam == 'free' else [1])
        bd.push({first[0]})
        order, gaps = [], []

        def candidates(k):
            rem = [e for e in E if e not in used]
            rng.shuffle(rem)
            if ENDS:
                bad = [e for e in rem if e in ENDS]
                good = [e for e in rem if e not in ENDS]
                nb_total = len(ENDS); half = nb_total // 2
                if k < half:
                    rem = bad
                elif k >= q - (nb_total - half):
                    rem = bad
                else:
                    rem = good
            if ADAPT:
                rem.sort(key=lambda e: -FAIL.get(e, 0) + rng.random() * 2)
            elif HARD:
                def unsafe(r):
                    return not (r == 1 or r % 4 == 3 or r % 16 == 1)
                def score(e):
                    a = e[0] if e[0] % 2 else e[1]; b = e[1] if e[0] % 2 else e[0]
                    return -(unsafe(a) + unsafe(h + 1 - b if h % 2 == 0 else h + 1 - a))
                rem.sort(key=lambda e: score(e) + rng.random() * 0.5)
            out = []
            for e in rem:
                if k == 0:
                    out.append((e, None))
                elif fam == 'gap':
                    for x in rng.sample([1, h], 2):
                        out.append((e, (1, x, h)))
                elif fam == 'free':
                    gs = [(a, b, c) for a in (1, h) for b in (1, h) for c in (1, h)]
                    rng.shuffle(gs)
                    for g in gs:
                        out.append((e, g))
                else:
                    for g in ((1, 1, 1), (h, h, h)) if True else ():
                        out.append((e, g))
            return out

        def place(e, g):
            n = 0
            if g is not None:
                for r in g:
                    n += 1
                    if not bd.push({r}):
                        return n, False
            n += 1
            if not bd.push(set(e)):
                return n, False
            return n, True

        stack.append(candidates(0))
        restart = False
        while stack:
            if nodes > maxn:
                restart = True
                break
            frame = stack[-1]
            if not frame:
                stack.pop()
                if order:
                    e = order.pop(); used.discard(e)
                    g = gaps.pop()
                    for _ in range(1 + (0 if g is None else 3)):
                        bd.pop()
                continue
            e, g = frame.pop()
            if fam == 'switch' and g is not None and gaps and gaps[-1] is not None and gaps[-1][0] == h and g[0] == 1:
                continue      # one switch only: once in row h, stay there
            nodes += 1
            n, ok = place(e, g)
            if not ok:
                for _ in range(n):
                    bd.pop()
                continue
            order.append(e); used.add(e); gaps.append(g)
            if len(order) > best_depth:
                best_depth = len(order)
                print('depth', best_depth, 'of', q, 'nodes', nodes, 'time', round(time.time() - t0), flush=True)
            if len(order) >= q - 6:
                lastleft[:] = sorted(set(E) - used)
            if len(order) >= q - 2:
                print('LEFT', sorted(set(E) - used), flush=True)
            if len(order) == q:
                endcell = 1 if fam == 'gap' else (rng.choice((1, h)) if fam == 'free' else (gaps[-1][0] if gaps[-1] else 1))
                if bd.push({endcell}):
                    word = ','.join(''.join(str(r) for r in sorted(c)) for c in bd.cols)
                    json.dump({'h': h, 'family': fam, 'w': len(bd.cols), 'word': word, 'order': order},
                              open('dfs_%s_h%d_s%d.json' % (fam, h, seed), 'w'))
                    print('FOUND width', len(bd.cols), 'order', order, flush=True)
                    return
                bd.pop()
                e = order.pop(); used.discard(e); gaps.pop()
                for _ in range(1 + (0 if g is None else 3)):
                    bd.pop()
                continue
            stack.append(candidates(len(order)))
        if not restart:
            print('exhausted', flush=True)
            return
        nodes = 0
        for e in lastleft:
            FAIL[e] = FAIL.get(e, 0) + 1
        print('restart', 'fail', sorted(FAIL.items(), key=lambda kv: -kv[1])[:6], flush=True)


if __name__ == '__main__':
    main()
