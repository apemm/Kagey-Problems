"""Search a valid block for one staircase L_g = {{a, a+g}}: its doubles at spacing s (any order), each gap's
sea cells chosen from {1, h, rows of the two neighbouring doubles}, W_h pad columns of a fixed row on each
side, full pair set F = K_{odd,even} (so the block is valid inside any larger board built the paper's way).
Usage: python block_dfs.py h g s leftpad rightpad seed maxnodes"""
import sys, random, json, time
from itertools import product
from dfs_gap import Board
LIMIT = 10 ** 9


def main():
    h, g, s, lp, rp, seed, maxn = map(int, sys.argv[1:8])
    rng = random.Random(seed)
    W = 1 + (h - 1) ** 2 // 4
    E = [(a, a + g) for a in range(1, h - g + 1)]
    q = len(E)
    t0 = time.time(); nodes = 0; best = 0
    while True:
        bd = Board(h)
        ok = True
        for _ in range(W):
            ok = ok and bd.push({lp})
        if not ok:
            print('left pad alone invalid'); return
        order, gaps, stack, used = [], [], [], set()

        def cands():
            rem = [e for e in E if e not in used]
            rng.shuffle(rem)
            out = []
            for e in rem:
                if not order:
                    out.append((e, ()))
                    continue
                prev = order[-1]
                rows = sorted({1, h, *prev, *e})
                gs = list(product(rows, repeat=s - 1))
                rng.shuffle(gs)
                out += [(e, gg) for gg in gs[:LIMIT]]
            return out

        stack.append(cands())
        restart = False
        while stack:
            if nodes > maxn:
                restart = True; break
            fr = stack[-1]
            if not fr:
                stack.pop()
                if order:
                    e = order.pop(); used.discard(e); gg = gaps.pop()
                    for _ in range(1 + len(gg)):
                        bd.pop()
                continue
            e, gg = fr.pop(); nodes += 1
            n = 0; good = True
            for r in gg:
                n += 1
                if not bd.push({r}):
                    good = False; break
            if good:
                n += 1
                good = bd.push(set(e))
            if not good:
                for _ in range(n):
                    bd.pop()
                continue
            order.append(e); used.add(e); gaps.append(gg)
            if len(order) > best:
                best = len(order); print('depth', best, 'of', q, 'nodes', nodes, flush=True)
            if len(order) == q:
                k = 0; good = True
                for _ in range(W):
                    k += 1
                    if not bd.push({rp}):
                        good = False; break
                if good:
                    word = ','.join(''.join(str(r) for r in sorted(c)) for c in bd.cols)
                    json.dump({'h': h, 'g': g, 's': s, 'pads': [lp, rp], 'w': len(bd.cols), 'word': word, 'order': order},
                              open('block_h%d_g%d_s%d_%d%d.json' % (h, g, s, lp, rp), 'w'))
                    print('FOUND', order, gaps, 'time', round(time.time() - t0), flush=True); return
                for _ in range(k):
                    bd.pop()
                e = order.pop(); used.discard(e); gg = gaps.pop()
                for _ in range(1 + len(gg)):
                    bd.pop()
                continue
            stack.append(cands())
        if not restart:
            print('exhausted (within the sampled sea choices)', flush=True); return
        nodes = 0


if __name__ == '__main__':
    main()
