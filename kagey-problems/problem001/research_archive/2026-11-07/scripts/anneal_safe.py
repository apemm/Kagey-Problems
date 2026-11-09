"""One-switch spacing-4 boards seeded by 2-adic safety (Lemma 8): row-1 part holds edges whose odd row a
is 1, = 3 mod 4 or = 1 mod 16; row-h part holds edges with h+1-b of that kind; unsafe edges go at the ends.
Then anneal the order and switch. Usage: python anneal_safe.py h steps seed"""
import sys, random, math, json, time
from fastcheck import violations
from anneal_split import build


def safe(r):
    return r == 1 or r % 4 == 3 or r % 16 == 1


def main():
    h, steps, seed = map(int, sys.argv[1:4]); rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    def odd(e): return e[0] if e[0] % 2 else e[1]
    def even(e): return e[1] if e[0] % 2 else e[0]
    low = [e for e in E if safe(odd(e)) and not safe(h + 1 - even(e))]
    both = [e for e in E if safe(odd(e)) and safe(h + 1 - even(e))]
    high = [e for e in E if not safe(odd(e)) and safe(h + 1 - even(e))]
    bad = [e for e in E if not safe(odd(e)) and not safe(h + 1 - even(e))]
    rng.shuffle(low); rng.shuffle(both); rng.shuffle(high)
    half = len(both) // 2
    order = bad[: len(bad) // 2] + low + both[:half] + both[half:] + high + bad[len(bad) // 2:]
    k0 = len(bad) // 2 + len(low) + half
    print('h', h, 'low', len(low), 'both', len(both), 'high', len(high), 'unsafe', bad, flush=True)
    M = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    cur = violations(h, build(h, order, k0, M)); best = cur; t0 = time.time()
    print('seed violations', cur, flush=True)
    for s in range(steps):
        T = 1.0 * (1 - s / steps) + 0.05
        o2, k2 = order[:], k0
        rr = rng.random()
        if rr < 0.45:
            i, j = rng.sample(range(len(o2)), 2); o2[i], o2[j] = o2[j], o2[i]
        elif rr < 0.9:
            i, j = rng.sample(range(len(o2)), 2); e = o2.pop(i); o2.insert(j, e)
        else:
            k2 = max(0, min(len(o2) - 1, k0 + rng.choice((-1, 1))))
        v = violations(h, build(h, o2, k2, M))
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            order, k0, cur = o2, k2, v
            if cur < best:
                best = cur; print('step', s, 'violations', cur, 'switch', k0, 'time', round(time.time() - t0), flush=True)
        if cur == 0:
            cols = build(h, order, k0, M)
            word = ','.join(''.join(str(r) for r in sorted(c)) for c in cols)
            json.dump({'h': h, 'w': len(cols), 'word': word, 'order': order, 'switch': k0}, open('safe_h%d_s%d.json' % (h, seed), 'w'))
            print('FOUND width', len(cols), 'order', order, 'switch', k0, flush=True); return
    print('END best', best, flush=True)


if __name__ == '__main__':
    main()
